-- Prove2me | Theorems.Thm_IsingLTL_BeliefProp_theorem_3_1_griffiths
-- name    : IsingLTL.BeliefProp.theorem_3_1_griffiths
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:16:49.472284+00:00
-- url     : https://prove2.me/theorems/c03fe000-920e-46d4-a9dd-49ed887502a3
-- title:
--   Griffiths' inequality (Theorem 3.1)
-- statement:
--   Let $V$ be a finite set and consider two Ising models $\mu$ and $\mu'$ on graphs $G=(V,E)$ and $G'=(V,E')$, with inverse temperatures $\beta,\beta'$ and magnetic fields $\{B_i\}$, $\{B'_i\}$. Assume $\beta\ge0$,
--
--   1. $E\subseteq E'$,
--   2. $\beta\le\beta'$,
--   3. $0\le B_i\le B'_i$ for all $i\in V$.
--
--   Then for every $U\subseteq V$,
--   $$0\le\Big\langle\mu,\prod_{i\in U}x_i\Big\rangle\le\Big\langle\mu',\prod_{i\in U}x_i\Big\rangle.$$
--
--   Griffiths' inequality is the monotonicity tool behind every comparison of boundary conditions in the paper: adding edges, raising the temperature parameter or raising the fields can only increase spin correlations.
--
--   **Formalization Note** The hypothesis $\beta\ge0$ is the paper's standing assumption (ferromagnetic model). No vertex is pinned.
-- source:
--   Dembo & Montanari, Ising Models on Locally Tree-Like Graphs, arXiv:0804.4726v3, p. 9, Theorem 3.1 (citing Liggett, Interacting Particle Systems, Theorem IV.1.21)

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_IsingModel

namespace IsingLTL.BeliefProp

/-- **Theorem 3.1 (Griffiths inequality)** (Dembo–Montanari, *Ising Models on Locally Tree-Like
Graphs*, arXiv:0804.4726v3, p. 9). Consider two Ising models `μ` and `μ′` on graphs `G = (V, E)`
and `G′ = (V, E′)`, inverse temperatures `β`, `β′` and fields `{B_i}`, `{B′_i}`. If `E ⊆ E′`,
`β ≤ β′` and `0 ≤ B_i ≤ B′_i` for all `i`, then `0 ≤ ⟨μ, ∏_{i∈U} x_i⟩ ≤ ⟨μ′, ∏_{i∈U} x_i⟩` for
every `U ⊆ V`.

Formalization Note: `V` is finite, `E ⊆ E′` is `G ≤ G′`, and the models are the Ising measures
(3.1) on the whole vertex set without pins. The hypothesis `0 ≤ β` is the paper's standing
assumption (ferromagnetic model, p. 1); it is not repeated in the theorem's sentence. -/
theorem theorem_3_1_griffiths {V : Type*} [Fintype V] [DecidableEq V]
    (G G' : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (β β' : ℝ) (B B' : V → ℝ) (hβ : 0 ≤ β) (hGG' : G ≤ G') (hββ' : β ≤ β')
    (hB : ∀ i, 0 ≤ B i) (hBB' : ∀ i, B i ≤ B' i) (U : Finset V) :
    0 ≤ IsingLTL.FreeEntropy.pairing (isingOn G β B ∅ Finset.univ) (fun x => ∏ i ∈ U, spinOf Finset.univ x i) ∧
      IsingLTL.FreeEntropy.pairing (isingOn G β B ∅ Finset.univ) (fun x => ∏ i ∈ U, spinOf Finset.univ x i) ≤
        IsingLTL.FreeEntropy.pairing (isingOn G' β' B' ∅ Finset.univ) (fun x => ∏ i ∈ U, spinOf Finset.univ x i) := by sorry

end IsingLTL.BeliefProp
