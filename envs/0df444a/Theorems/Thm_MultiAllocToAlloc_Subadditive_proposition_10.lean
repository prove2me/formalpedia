-- Prove2me | Theorems.Thm_MultiAllocToAlloc_Subadditive_proposition_10
-- name    : MultiAllocToAlloc.Subadditive.proposition_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T18:10:27.976594+00:00
-- url     : https://prove2.me/theorems/a79fd417-eb4f-4a35-8a1e-76da4c4a7235
-- title:
--   Proposition 10 — ω(S_p, M, v) + ω(S_q, M, v) ≥ v(M) for subadditive v
-- statement:
--   Let $M$ be a finite set of items and $v$ a valuation. A valuation v assigns a real number to every set of items and is normalized (v(∅) = 0) and monotone (v(S) ≤ v(T) for S ⊆ T), the paper's standing assumptions (p. 1, and §2.1, p. 6); it is subadditive when v(S ∪ T) ≤ v(S) + v(T) for all S, T. Here ω(S_p, M, v) and ω(S_q, M, v) (Definition 7, p. 6) are the maximin values that a player p with valuation v (her payoff is v(T) for the set T of items she picks; the opponent q's payoff is −v(T)) can guarantee in the picking game on the finite item set M with the alternating picking sequence of length |M| that starts with p (S_p) or with q (S_q); every item of M is picked. If $v$ is subadditive, then
--   $$\omega(S_p,M,v)+\omega(S_q,M,v)\ \ge\ v(M).$$
--
--   Differences from the source:
--   - encoding: a valuation v defined on the subsets of the game's item set M → v : Finset (Fin m) → ℝ defined on all subsets of the ambient items Fin m, with M : Finset (Fin m) and the normalization, monotonicity (and subadditivity) hypotheses stated for all subsets; reason: ω(S, M, v) depends only on the values of v on subsets of M, and every normalized monotone (subadditive) valuation on the subsets of M extends to Fin m with the same properties via T ↦ v(T ∩ M); same instances
-- source:
--   Feige, arXiv:2506.21493v1, Proposition 10, p. 8

import Mathlib
import Definitions.Def_SubmodOrder_Subadditive
import Definitions.Def_MultiAllocToAlloc_Subadditive_Valuation
import Definitions.Def_MultiAllocToAlloc_Subadditive_PickingGame

namespace MultiAllocToAlloc.Subadditive

/-- Feige, arXiv:2506.21493v1, Proposition 10, p. 8: for a normalized monotone subadditive `v`,
`ω(S_p, M, v) + ω(S_q, M, v) ≥ v(M)`. -/
theorem proposition_10 {m : ℕ} (M : Finset (Fin m)) (v : Finset (Fin m) → ℝ)
    (hnorm : IsNormalized v) (hmono : IsMonotone v) (hsub : SubmodOrder.Subadditive v) :
    v M ≤ omegaP v M + omegaQ v M := by sorry

end MultiAllocToAlloc.Subadditive
