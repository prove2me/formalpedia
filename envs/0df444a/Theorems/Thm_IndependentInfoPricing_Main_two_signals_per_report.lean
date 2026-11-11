-- Prove2me | Theorems.Thm_IndependentInfoPricing_Main_two_signals_per_report
-- name    : IndependentInfoPricing.Main.two_signals_per_report
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:32:16.530866+00:00
-- url     : https://prove2.me/theorems/205089a7-3192-4118-92ac-1c7fb5eaff06
-- title:
--   Lemma 2.1 — Two signals per report suffice
-- statement:
--   Consider an IC direct information mechanism with both free outside options, a report $v$, and the arbitrary measurable experiment assigned to that report. There exists a measurable action event $A$ giving the optimal payoff to $v$. Merging that event and its complement produces a binary vector $x_i=\Pr(A\mid i)$ in $[0,1]^Q$ with
--
--   $$V(v,x)=\operatorname{Value}(E,v),\qquad V(w,x)\le\operatorname{Value}(E,w)\quad\text{for every type }w.$$
--
--   Replacing just that report's experiment preserves full IC and both participation inequalities. Its price function is exactly the original price function, so its nonnegative expected revenue is unchanged under every type law. The event itself attains the intended type's payoff, so following its recommendation is optimal. This permits the binary operational model used in subsequent statements without restricting the original signal space.
--
--   Differences from the source:
--   - encoding: arbitrary measurable signals and binary recommendation merging at one report → measurable action event, its statewise probabilities, and a replaced gross-payoff table using the unchanged price function; reason: a binary action rule is a measurable act-event; IC and both IR comparisons are asserted for the replacement and unchanged prices preserve revenue
-- source:
--   Hu Fu, Chenshuo Guo, STOC 2027 submission #1459 (October 2026), Lemma 2.1, printed pp.6–7 (PDF pp.8–9); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1459.pdf

import Definitions.Def_IndependentInfoPricing_Main_Menus

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace IndependentInfoPricing.Main

/-- Lemma 2.1, pp.6–7 (PDF 8–9): one report's experiment is compressed at its unchanged price. -/
theorem two_signals_per_report {Q : ℕ} {S : Type} [MeasurableSpace S]
    (m : ExperimentMechanism (Fin Q) S) (hm : ExperimentICIR m) (v : Values (Fin Q)) :
    ∃ A : Set S, MeasurableSet A ∧
      (∀ i, compress (m.experiment v) A i ∈ Set.Icc (0 : ℝ) 1) ∧
      responsePayoff (m.experiment v) v A = experimentValue (m.experiment v) v ∧
      binaryValue v (compress (m.experiment v) A) = experimentValue (m.experiment v) v ∧
      (∀ w, binaryValue w (compress (m.experiment v) A) ≤ experimentValue (m.experiment v) w) ∧
      GrossICIR (replacedGross m v (compress (m.experiment v) A)) m.price := by sorry

end IndependentInfoPricing.Main
