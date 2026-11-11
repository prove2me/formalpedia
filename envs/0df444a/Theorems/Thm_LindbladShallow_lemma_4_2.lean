-- Prove2me | Theorems.Thm_LindbladShallow_lemma_4_2
-- name    : LindbladShallow.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:14:23.166234+00:00
-- url     : https://prove2.me/theorems/58aed693-466f-4d20-93c3-52e6f6d2ca9e
-- title:
--   Lemma 4.2 — sequential composition of transducers
-- statement:
--   Let $\mathcal H$ be a public space and $\mathcal L_1,\dots,\mathcal L_L$ mutually orthogonal private spaces. Suppose each unitary $S_j$ on $\mathcal H\oplus\mathcal L_j$ satisfies $S_j\binom{I}{\gamma_j}=\binom{V_j}{\gamma_j}$ with $V_j$ on $\mathcal H$. Extend each $S_j$ by the identity on the other private spaces. Then $S=S_L\cdots S_1$ satisfies
--   $$S\begin{pmatrix}I\\\Gamma\end{pmatrix}=\begin{pmatrix}V\\\Gamma\end{pmatrix},\qquad V=V_L\cdots V_1,\qquad \Gamma x=\bigoplus_{j=1}^L\gamma_jV_{j-1}\cdots V_1x,$$
--   with empty products the identity.
--
--   This composes the per-occurrence transducers of a window into one transducer for the whole window.
--
--   Differences from the source:
--   - encoding: mutually orthogonal private spaces 𝓛_1, …, 𝓛_L → the summands of a sigma type Σ j, κ j with 0-based indices; reason: Lean indexing; same spaces
-- source:
--   Shen, Wu, Yuan, Zhang, Shallow Quantum Circuits for Geometrically Local Lindblad Dynamics, arXiv:2610.05362 (held version, sha256 8f4637ef…), Lemma 4.2, p.26

import Mathlib
import Definitions.Def_LindbladShallow_dnorm
import Definitions.Def_LindbladShallow_extendPriv

open scoped Matrix ComplexOrder

namespace LindbladShallow

/-- **Lemma 4.2** (Sequential composition; arXiv:2610.05362, held version sha256 8f4637ef…, p.26).
Let `ℋ` be a common public space and `𝓛_1, …, 𝓛_L` mutually orthogonal private spaces. Suppose
each unitary `S_j` on `ℋ ⊕ 𝓛_j` satisfies `S_j (I; γ_j) = (V_j; γ_j)` with `V_j` acting on `ℋ`.
Extend each `S_j` by the identity on all other private spaces. Then `S = S_L ⋯ S_1` satisfies
`S (I; Γ) = (V; Γ)` with `V = V_L ⋯ V_1` and `Γx = ⊕_{j=1}^L γ_j V_{j−1} ⋯ V_1 x` (empty products
are the identity).

**Formalization Note** The private spaces are the summands of `Σ j, κ j`; indices are 0-based, so
the block of summand `j` is `γ_j` times the product of the `V_i` with `i < j`. -/
theorem lemma_4_2 {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ℕ} {κ : Fin L → Type*}
    [∀ k, Fintype (κ k)] [∀ k, DecidableEq (κ k)]
    (S : ∀ j, Matrix (ι ⊕ κ j) (ι ⊕ κ j) ℂ) (V : Fin L → Matrix ι ι ℂ)
    (γ : ∀ j, Matrix (κ j) ι ℂ) (hS : ∀ j, S j ∈ Matrix.unitaryGroup (ι ⊕ κ j) ℂ)
    (hSγ : ∀ j, S j * Matrix.fromRows 1 (γ j) = Matrix.fromRows (V j) (γ j)) :
    let Γ : Matrix (Σ k, κ k) ι ℂ := fun p x =>
      (γ p.1 * orderedProd (((List.finRange L).filter fun i => i < p.1).map V)) p.2 x
    orderedProd (List.ofFn fun j => extendPriv j (S j)) * Matrix.fromRows 1 Γ =
      Matrix.fromRows (orderedProd (List.ofFn V)) Γ := by sorry

end LindbladShallow
