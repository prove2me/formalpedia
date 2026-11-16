-- Prove2me | Theorems.Thm_HouseAllocLT_LowerBound_Supplement_lemma_4_8
-- name    : HouseAllocLT.LowerBound.Supplement.lemma_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T14:19:33.119524+00:00
-- url     : https://prove2.me/theorems/b5cacad1-0a54-4541-80b2-5dc5c343912d
-- title:
--   Lemma 4.8 — RPG matches a (1 − 1/e) fraction when the benchmark is perfect
-- statement:
--   Let $m\ge1$ and fix a routine. Suppose a profile on $r$ agents has a rank-maximal benchmark that matches every agent and every list ends at its benchmark class. Then
--   $$\mathbb E\,|\mathrm{RPG}|\ge(1-e^{-1})\,r,$$
--   the expectation over the uniform order of the $r$ agents.
--
--   This is the size bound used in Lemma 4.10.
--
--   Differences from the source:
--   - encoding: ranks and classes numbered from one → classes numbered from zero (paper rank j is class j−1); reason: a bijection of indices, no instance changes
--   - encoding: a fixed deterministic maximum-matching routine → a universally quantified routine `MM`; reason: the source states the result for whatever fixed routine RPG uses, which is the same claim
--   - encoding: "a rank-maximal benchmark that matches everyone" with benchmark classes → a rank-maximal M* with a rank function R such that each agent i receives an object of its class R_i; reason: R_i is determined by M*, and the hypothesis forces every agent to be matched
-- source:
--   Jinshan Zhang, Nan Zhao, Hao Xu, Meng Xi, Lin Zhao, STOC 2027 submission #174 (October 2026), Lemma 4.8, PDF p. 13 (printed p. 11); proof PDF pp. 18–20 (printed pp. 16–18); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/174.pdf

import Definitions.Def_HouseAllocLT_LowerBound_Supplement_RPG

open scoped BigOperators ENNReal
open Classical

namespace HouseAllocLT.LowerBound.Supplement
open HouseAllocLT.LowerBound

/-- Lemma 4.8, PDF p. 13 (printed p. 11). If a profile on `r` agents has a rank-maximal benchmark
`M*` that matches everyone (agent `i` in class `R_i`) and every list ends at its benchmark class,
then `E[|RPG|] ≥ (1 − e^{−1}) r`. -/
theorem lemma_4_8 {r m : ℕ} (hm : 1 ≤ m) (MM : MaxMatchingRoutine r m)
    (Q : Profile r m) (Mstar : Assignment r m) (hRM : RankMaximal Q Mstar)
    (R : Fin r → ℕ) (hR : ∀ i, ∃ a ∈ (Q i).classes (R i), (i, a) ∈ Mstar)
    (hend : ∀ i, (Q i).length = R i + 1) :
    (1 - Real.exp (-1)) * (r : ℝ) ≤ expectedSize (rpg MM) Q := by sorry

end HouseAllocLT.LowerBound.Supplement
