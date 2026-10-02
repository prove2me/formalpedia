-- Prove2me | Theorems.Thm_MDPFinance_Contracting_theorem_7_3_4
-- name    : MDPFinance.Contracting.theorem_7_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:46:19.416639+00:00
-- url     : https://prove2.me/theorems/68971fc3-4632-4c92-b75d-69fd9d1a84b9
-- title:
--   Theorem 7.3.4 (Verification Theorem) — the contracting-model sharpening of Theorem 7.1.7
-- statement:
--   Under a genuine bounding function with $\beta\alpha_b < 1$, the verification theorem (Theorem
--   7.1.7) sharpens: the hypothesis "$v \ge J_\infty$" is no longer needed. Any fixed point $v \in
--   IB_b$ of $T$ automatically satisfies $v = J_\infty = J$ once a maximizer of $v$ is exhibited —
--   contraction alone forces uniqueness, so there is no need to separately verify $v$ dominates the
--   true value. This is the direct predecessor of the goal (Theorem 7.3.5), isolating exactly the
--   "single fixed point" case before the goal generalizes to an entire closed invariant class $IM$.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 207, Theorem 7.3.4

import Mathlib
import Definitions.Def_MDPFinance_Contracting_Model
import Definitions.Def_MDPFinance_Contracting_Value
import Definitions.Def_MDPFinance_Contracting_Bounding

open MeasureTheory ProbabilityTheory

namespace MDPFinance.Contracting

/-- Theorem 7.3.4 (Verification Theorem) (Bäuerle–Rieder, p. 207, PDF 218). Let `b` be a bounding
function, `\beta\alpha_b < 1` and `v \in IB_b` be a fixed point of `T : IB_b \to IB_b`. If `f^*`
is a maximizer of `v` (of the `EReal`-valued `T`, `v` cast up via the coercion), then
`v = J_\infty = J` and `(f^*,f^*,\dots)` is an optimal stationary policy. -/
theorem theorem_7_3_4 {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] (M : MarkovDecisionModel E A)
    (b : E → ℝ) (cr αb : ℝ) (hb : IsBoundingFunction M b cr αb) (hαb : M.β * αb < 1)
    (v : E → ℝ) (hvIBb : v ∈ IBb b) (hvfix : ∀ x, T M (fun y => (v y : EReal)) x = (v x : EReal))
    (fstar : E → A) (hfstar : IsMaximizerOf M (fun y => (v y : EReal)) fstar) :
    (∀ x, (v x : EReal) = Jinf M x) ∧ (∀ x, (v x : EReal) = Jlim M x) ∧
      ∀ x, Jinfpi M M.r (fun _ => fstar) x = Jinf M x := by sorry

end MDPFinance.Contracting
