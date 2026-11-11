-- Prove2me | Theorems.Thm_LindbladShallow_lemma_4_1
-- name    : LindbladShallow.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:14:17.392023+00:00
-- url     : https://prove2.me/theorems/e0427117-1ed5-493c-b4b4-b9217232fe70
-- title:
--   Lemma 4.1 — weighted Cayley identity
-- statement:
--   Let $K=K^\dagger$ with $\|K\|\le\tfrac12$ and $0\preceq\Theta\preceq I$ on a finite-dimensional cell space, and let $O,q_0,R_\Theta,S_\Theta,H_\Theta,D_\Theta,\gamma$ be as in §4.1. Then $S_\Theta$ and $V_\Theta=(I-iH_\Theta)D_\Theta^{-1}$ are unitary,
--   $$S_\Theta\begin{pmatrix}I\\\gamma\end{pmatrix}=\begin{pmatrix}V_\Theta\\\gamma\end{pmatrix},\qquad \gamma^\dagger\gamma=2D_\Theta^{-\dagger}\Theta D_\Theta^{-1}.$$
--
--   The transducer $S_\Theta$ realizes the physical Cayley collision gates (Hamiltonian and jump) on both vacuum and occupied baths, with a catalyst $\gamma$ that the finite-reuse construction exploits.
--
--   Differences from the source:
--   - encoding: the private space ℂ²_Q ⊗ ℋ_cell → ℋ_cell ⊕ ℋ_cell, first summand Q = 0; reason: canonical isomorphism; same operators
--   - encoding: √Θ, √(I − K²), inverses → continuous functional calculus square roots and Mathlib matrix inverses; reason: all inverted matrices are invertible under the hypotheses
-- source:
--   Shen, Wu, Yuan, Zhang, Shallow Quantum Circuits for Geometrically Local Lindblad Dynamics, arXiv:2610.05362 (held version, sha256 8f4637ef…), Lemma 4.1, p.24; definitions pp.23–24

import Mathlib
import Definitions.Def_LindbladShallow_dnorm
import Definitions.Def_LindbladShallow_transducer

open scoped Matrix ComplexOrder

namespace LindbladShallow

/-- **Lemma 4.1** (Weighted Cayley identity; arXiv:2610.05362, held version sha256 8f4637ef…,
p.24, with the setting of pp.23–24). Let `K = K†` with `‖K‖ ≤ 1/2` and `0 ⪯ Θ ⪯ I` on a
finite-dimensional cell space. With `O`, `q₀`, `P`, `t`, `b`, `R_Θ`, `S_Θ := R_Θ(I ⊕ O)`,
`H_Θ := √Θ K √Θ`, `D_Θ := I + iH_Θ`, `γ := (I + iO)q₀√Θ D_Θ^{−1}` as on p.24, both `S_Θ` and
`V_Θ = (I − iH_Θ)D_Θ^{−1}` are unitary, `S_Θ (I; γ) = (V_Θ; γ)`, and `γ†γ = 2D_Θ^{−†} Θ D_Θ^{−1}`.

**Formalization Note** `Θ` need not commute with `K`. Square roots are by continuous functional
calculus. The private space `ℂ²_Q ⊗ ℋ_cell` is `ℋ_cell ⊕ ℋ_cell` (first summand `Q = 0`). -/
theorem lemma_4_1 {ι : Type*} [Fintype ι] [DecidableEq ι] (K Θ : Matrix ι ι ℂ)
    (hK : K.IsHermitian) (hKn : opNorm K ≤ 1 / 2) (hΘ : Θ.PosSemidef) (hΘI : (1 - Θ).PosSemidef) :
    transS K Θ ∈ Matrix.unitaryGroup (ι ⊕ (ι ⊕ ι)) ℂ ∧
      transV K Θ ∈ Matrix.unitaryGroup ι ℂ ∧
      transS K Θ * Matrix.fromRows 1 (transGamma K Θ) =
        Matrix.fromRows (transV K Θ) (transGamma K Θ) ∧
      Matrix.conjTranspose (transGamma K Θ) * transGamma K Θ =
        (2 : ℂ) • (Matrix.conjTranspose (transD K Θ)⁻¹ * Θ * (transD K Θ)⁻¹) := by sorry

end LindbladShallow
