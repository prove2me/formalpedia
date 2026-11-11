-- Prove2me | Theorems.Thm_IndependentInfoPricing_Main_simple_benchmark_exact
-- name    : IndependentInfoPricing.Main.simple_benchmark_exact
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:33:37.197421+00:00
-- url     : https://prove2.me/theorems/6a1ff617-0076-4523-acfc-ee0df8ff68b7
-- title:
--   Lemma 3.2 — The simple benchmark is exactly a₀
-- statement:
--   For the actual Section 3.1 family with integer $k\ge1$ and the prescribed support-size lower bound, the displayed masses of $X$ are nonnegative and sum to one. Both $X$ and $Y$ are probability laws with finite strictly positive supports. For every price $p\ge0$,
--
--   $$p\Pr(X\ge p)\Pr(Y\ge p)\le a,$$
--
--   and equality is attained at some such price. The paper's ensuing benchmark identities are also retained:
--
--   $$R=\widetilde R=a.$$
--
--   All probabilities are computed from the explicit family, rather than assumed from its target survival identities. These statements validate the constructed distribution and pin down the denominator in the separation result.
--
--   Differences from the source:
--   - encoding: real expected revenues and independent coordinates indexed by [Q] → nonnegative extended integrals and suprema with coordinates indexed by Fin Q; reason: preserves arbitrary real product laws and infinite revenues without default-zero integration; Fin Q only relabels the finite states
-- source:
--   Hu Fu, Chenshuo Guo, STOC 2027 submission #1459 (October 2026), Lemma 3.2, printed pp.13–13 (PDF pp.15–15); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1459.pdf

import Definitions.Def_IndependentInfoPricing_Main_Diagonal

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace IndependentInfoPricing.Main

/-- Lemma 3.2 and (19)–(28), pp.12–14 (PDF 14–16). -/
theorem simple_benchmark_exact (k n : ℕ) (h : FamilyParameters k n) :
    PositiveFiniteLaw (familyX k n) ∧ PositiveFiniteLaw (familyY k n) ∧
    (∀ i ∈ Finset.Icc 1 n, 0 ≤ massX k n i) ∧
    (∑ i ∈ Finset.Icc 1 n, massX k n i) = 1 ∧
    (∀ p : ℝ, 0 ≤ p →
      ENNReal.ofReal p * familyX k n (Set.Ici p) * familyY k n (Set.Ici p) ≤ ENNReal.ofReal (baseA k)) ∧
    (∃ p : ℝ, 0 ≤ p ∧
      ENNReal.ofReal p * familyX k n (Set.Ici p) * familyY k n (Set.Ici p) = ENNReal.ofReal (baseA k)) ∧
    benchmark (familyLaw k n) = ENNReal.ofReal (baseA k) ∧
    benchmarkSym (familyLaw k n) = ENNReal.ofReal (baseA k) := by sorry

end IndependentInfoPricing.Main
