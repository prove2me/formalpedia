-- Prove2me | Theorems.Thm_MultiAllocToAlloc_Subadditive_proposition_8
-- name    : MultiAllocToAlloc.Subadditive.proposition_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T18:10:22.623199+00:00
-- url     : https://prove2.me/theorems/c563a201-2b2d-4085-a7ec-3ac90dfad001
-- title:
--   Proposition 8 — first-mover advantage: ω(S_p, M, v) ≥ ω(S_q, M, v)
-- statement:
--   Let $M$ be a finite set of items and $v$ a valuation. A valuation v assigns a real number to every set of items and is normalized (v(∅) = 0) and monotone (v(S) ≤ v(T) for S ⊆ T), the paper's standing assumptions (p. 1, and §2.1, p. 6). Here ω(S_p, M, v) and ω(S_q, M, v) (Definition 7, p. 6) are the maximin values that a player p with valuation v (her payoff is v(T) for the set T of items she picks; the opponent q's payoff is −v(T)) can guarantee in the picking game on the finite item set M with the alternating picking sequence of length |M| that starts with p (S_p) or with q (S_q); every item of M is picked. Then
--   $$\omega(S_p,M,v)\ \ge\ \omega(S_q,M,v).$$
--
--   Differences from the source:
--   - encoding: a valuation v defined on the subsets of the game's item set M → v : Finset (Fin m) → ℝ defined on all subsets of the ambient items Fin m, with M : Finset (Fin m) and the normalization, monotonicity (and subadditivity) hypotheses stated for all subsets; reason: ω(S, M, v) depends only on the values of v on subsets of M, and every normalized monotone (subadditive) valuation on the subsets of M extends to Fin m with the same properties via T ↦ v(T ∩ M); same instances
-- source:
--   Feige, arXiv:2506.21493v1, Proposition 8, p. 6

import Mathlib
import Definitions.Def_MultiAllocToAlloc_Subadditive_Valuation
import Definitions.Def_MultiAllocToAlloc_Subadditive_PickingGame

namespace MultiAllocToAlloc.Subadditive

/-- Feige, arXiv:2506.21493v1, Proposition 8, p. 6: for every normalized monotone valuation `v`
and every finite item set `M`, `ω(S_p, M, v) ≥ ω(S_q, M, v)`. -/
theorem proposition_8 {m : ℕ} (M : Finset (Fin m)) (v : Finset (Fin m) → ℝ)
    (hnorm : IsNormalized v) (hmono : IsMonotone v) :
    omegaQ v M ≤ omegaP v M := by sorry

end MultiAllocToAlloc.Subadditive
