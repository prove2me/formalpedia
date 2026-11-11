-- Prove2me | Theorems.Thm_IndependentInfoPricing_Main_unbounded_separation
-- name    : IndependentInfoPricing.Main.unbounded_separation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:33:50.414636+00:00
-- url     : https://prove2.me/theorems/7b5c7dd4-4459-4a99-a097-7e14e6d438c4
-- title:
--   Theorem 3.1 — Unbounded separation
-- statement:
--   For every real $K>0$ there exist independent, finitely supported strictly positive magnitudes $X,Y$. For the two-coordinate type $v=(X,-Y)$ their product law satisfies
--
--   $$\operatorname{OPT}>K\widetilde R.$$
--
--   The optimum uses full information IC and both free outside options. The benchmark is the better of actual symmetrized separate selling and priced full revelation, selected before the buyer's type is observed. There are no density, regularity or half-tail hypotheses on this existential instance. This proves the negative clause of the headline theorem.
--
--   Differences from the source:
--   - encoding: real expected revenues and independent coordinates indexed by [Q] → nonnegative extended integrals and suprema with coordinates indexed by Fin Q; reason: preserves arbitrary real product laws and infinite revenues without default-zero integration; Fin Q only relabels the finite states
-- source:
--   Hu Fu, Chenshuo Guo, STOC 2027 submission #1459 (October 2026), Theorem 3.1, printed pp.11–11 (PDF pp.13–13); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1459.pdf

import Definitions.Def_IndependentInfoPricing_Main_Diagonal

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace IndependentInfoPricing.Main

/-- Theorem 3.1, p.11 (PDF 13): two independent, finitely supported positive magnitudes. -/
theorem unbounded_separation (K : ℝ) (hK : 0 < K) :
    ∃ X Y : Measure ℝ, PositiveFiniteLaw X ∧ PositiveFiniteLaw Y ∧
      ENNReal.ofReal K * benchmarkSym (productLaw (oppositeLaw X Y)) < opt (productLaw (oppositeLaw X Y)) := by sorry

end IndependentInfoPricing.Main
