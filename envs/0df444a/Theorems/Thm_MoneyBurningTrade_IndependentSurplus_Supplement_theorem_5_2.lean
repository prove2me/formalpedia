-- Prove2me | Theorems.Thm_MoneyBurningTrade_IndependentSurplus_Supplement_theorem_5_2
-- name    : MoneyBurningTrade.IndependentSurplus.Supplement.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:45:18.045115+00:00
-- url     : https://prove2.me/theorems/ea47cfc9-b607-48a8-9f91-46bc935c587f
-- title:
--   Theorem 5.2 — correlated values: WBB cannot approximate first-best social welfare
-- statement:
--   For every $\varepsilon>0$ there is a correlated joint probability law $F$ of the seller's and buyer's values on $[0,1]^2$, not the product of its two marginals, such that for every interval value space $V\subseteq\mathbb R_{\ge0}$ carrying all of $F$'s mass (for instance $V=[0,1]$), every measurable randomized mechanism $M$ on $V$ that is dominant-strategy incentive compatible, individually rational and weakly budget balanced (strongly budget-balanced ones included) satisfies
--
--   $$\mathrm{TU}_M(F)\le\mathrm{SW}_M(F)<\varepsilon\cdot\mathrm{SW}_{\mathrm{OPT}}(F)=\varepsilon\cdot\mathrm{TU}_{\mathrm{OPT}}(F),$$
--
--   and all objectives of $M$ are finite. Here $\mathrm{TU}$ is the traders' utility (burnt money excluded), $\mathrm{SW}$ the social welfare (burnt money included) and $\mathrm{SW}_{\mathrm{OPT}}=\mathbb E[\max\{v_s,v_b\}]$; the first best burns no money, so $\mathrm{TU}_{\mathrm{OPT}}=\mathrm{SW}_{\mathrm{OPT}}$ by definition. The law is chosen before the value space and the mechanism.
--
--   Thus even with money burning, no dominant-strategy mechanism guarantees a constant fraction of the first-best social welfare when values are correlated.
--
--   Differences from the source:
--   - reading: a correlated distribution F (the word is not defined) → a probability law μ on ℝ² with μ ≠ (marginal of v_s) ⊗ (marginal of v_b); reason: the values are not independent; this is the standard meaning, and the witness F^n of (28) satisfies it
--   - generalization: every WBB DSIC and IR mechanism for F, value space unnamed → a law concentrated on [0,1]², and for every interval value space T ⊆ [0, ∞) with μ((T × T)ᶜ) = 0, every DSIC, IR, WBB mechanism on T; reason: T = [0, 1] is one admissible value space, so the statement specializes to the source claim read on [0, 1]; the source argument evaluates the mechanism only on the support interval [q_0, 1] ⊆ T
--   - encoding: expectations of the objectives → Bochner integrals together with finite-objective (integrability) conclusions for every admissible mechanism; reason: (9) bounds payments and surpluses on a bounded value square, so all are finite; stating it as a conclusion excludes no competitor and rules out the default value 0 of a non-integrable integral
--   - encoding: the closing equality ε·SW_OPT = ε·TU_OPT → stated through SW_OPT only; reason: §3.3 (printed p. 17) defines TU_OPT(F) = SW_OPT(F); the equality is definitional
-- source:
--   Moshe Babaioff, Noam Nisan, Ariel Shaulker, STOC 2027 submission #303 (October 2026), Theorem 5.2 (= Theorem 3, statement 2, of the introduction, printed p. 6); proof in §5.2, printed pp. 33–34, printed p. 32 (PDF p. 33); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/303.pdf

import Mathlib
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_Supplement_JointObjectives
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_IsDSIC
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_IsIR
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_IsWBB

open MeasureTheory

set_option autoImplicit false

namespace MoneyBurningTrade.IndependentSurplus.Supplement

/-- Theorem 5.2, §5 p.32: for every `ε > 0` there is a correlated joint law `F` on
`[0,1]²` (not the product of its marginals) such that, for every interval value space `T ⊆ ℝ≥0` carrying
all of `F`'s mass (`[0,1]` among them), every DSIC, IR, WBB mechanism `M` on `T`
(SBB ones included) has `TU_M(F) ≤ SW_M(F) < ε·SW_OPT(F)`. By the paper's
definition `TU_OPT = SW_OPT`. The law precedes the competitor; integrability of every
objective is a conclusion. -/
theorem theorem_5_2 (ε : ℝ) (hε : 0 < ε) :
    ∃ μ : Measure (ℝ × ℝ),
      IsProbabilityMeasure μ ∧ μ (reportInterval ×ˢ reportInterval)ᶜ = 0 ∧
      μ ≠ (μ.map Prod.fst).prod (μ.map Prod.snd) ∧
      ∀ T : Set ℝ, T ⊆ Set.Ici 0 → T.OrdConnected → μ (T ×ˢ T)ᶜ = 0 →
      ∀ M : SecondBestBT.Mechanism,
        IsMechanism T M → IsDSIC T M → IsIR T M → IsWBB T M →
        FiniteJointObjectives μ M ∧
        TU μ M ≤ SW μ M ∧ SW μ M < ε * firstBestSW μ := by sorry

end MoneyBurningTrade.IndependentSurplus.Supplement
