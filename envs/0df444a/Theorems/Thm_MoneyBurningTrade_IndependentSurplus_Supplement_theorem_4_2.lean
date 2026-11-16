-- Prove2me | Theorems.Thm_MoneyBurningTrade_IndependentSurplus_Supplement_theorem_4_2
-- name    : MoneyBurningTrade.IndependentSurplus.Supplement.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:39:23.880135+00:00
-- url     : https://prove2.me/theorems/50d0312d-1f1e-46ce-a465-4d310885941f
-- title:
--   Theorem 4.2 — correlated values: WBB beats every SBB mechanism in traders’ utility
-- statement:
--   For every $\varepsilon>0$ there exist a joint probability law $F$ of the seller's and buyer's values on $[0,1]^2$ (values may be correlated) and a measurable randomized mechanism $M_{\mathrm{WBB}}$ on $[0,1]$ that is dominant-strategy incentive compatible, individually rational and weakly budget balanced, such that every measurable randomized mechanism $M_{\mathrm{SBB}}$ on $[0,1]$ that is dominant-strategy incentive compatible, individually rational and strongly budget balanced satisfies
--
--   $$\varepsilon\cdot\mathrm{TU}_{M_{\mathrm{WBB}}}(F)>\mathrm{TU}_{M_{\mathrm{SBB}}}(F)=\mathrm{SW}_{M_{\mathrm{SBB}}}(F).$$
--
--   Here $\mathrm{TU}$ is the traders' utility $u_b+u_s$, which does not count burnt money, and $\mathrm{SW}$ the social welfare. All objectives of both mechanisms are finite. The law and $M_{\mathrm{WBB}}$ are chosen before the competitor.
--
--   This is the correlated-values counterpart of Theorem 4.1: money burning can make the traders arbitrarily better off in total utility.
--
--   Differences from the source:
--   - reading: existential common value interval V and joint law F → witness value interval [0,1] = reportInterval, a Borel probability law on ℝ² concentrated on [0,1]²; reason: §3.1 lets V be any interval of nonnegative reals and the theorem does not name it; it is read as the existence of an instance, as in its proof (§4.3 uses Lemma 4.3 on [0,1]), the same reading as the published goal; every measurable randomized competitor on [0,1] is retained
--   - encoding: expectations of the objectives → Bochner integrals together with finite-objective (integrability) conclusions for every admissible mechanism; reason: (9) bounds payments and surpluses on a bounded value square, so all are finite; stating it as a conclusion excludes no competitor and rules out the default value 0 of a non-integrable integral
-- source:
--   Moshe Babaioff, Noam Nisan, Ariel Shaulker, STOC 2027 submission #303 (October 2026), Theorem 4.2 (= Theorem 2 of the introduction, printed p. 4); proof in §4.3, printed pp. 30–31, printed p. 18 (PDF p. 19); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/303.pdf

import Mathlib
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_Supplement_JointObjectives
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_IsDSIC
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_IsIR
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_IsWBB
import Definitions.Def_SecondBestBT_IsSBB

open MeasureTheory

set_option autoImplicit false

namespace MoneyBurningTrade.IndependentSurplus.Supplement

/-- Theorem 4.2, §4 p.18: for every `ε > 0` there are a joint law `F` on `[0,1]²`
and one DSIC, IR, WBB mechanism `W` such that every DSIC, IR, SBB mechanism `M`
(measurable, randomized, on the whole report interval) has
`TU_M(F) < ε·TU_W(F)` and `TU_M(F) = SW_M(F)`. Witnesses precede the competitor;
integrability of every objective is a conclusion. -/
theorem theorem_4_2 (ε : ℝ) (hε : 0 < ε) :
    ∃ (μ : Measure (ℝ × ℝ)) (W : SecondBestBT.Mechanism),
      IsProbabilityMeasure μ ∧ μ (reportInterval ×ˢ reportInterval)ᶜ = 0 ∧
      IsMechanism reportInterval W ∧ IsDSIC reportInterval W ∧
      IsIR reportInterval W ∧ IsWBB reportInterval W ∧
      FiniteJointObjectives μ W ∧
      ∀ M : SecondBestBT.Mechanism,
        IsMechanism reportInterval M → IsDSIC reportInterval M →
        IsIR reportInterval M → SecondBestBT.IsSBB reportInterval M →
        FiniteJointObjectives μ M ∧
        TU μ M < ε * TU μ W ∧ TU μ M = SW μ M := by sorry

end MoneyBurningTrade.IndependentSurplus.Supplement
