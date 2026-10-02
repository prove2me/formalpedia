-- Prove2me | Theorems.Thm_MDPFinance_LPDuality_corollary_7_5_3
-- name    : MDPFinance.LPDuality.corollary_7_5_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:53:05.884977+00:00
-- url     : https://prove2.me/theorems/082760ad-d427-4116-8ebd-84c26cb35f65
-- title:
--   Corollary 7.5.3 — Howard's algorithm converges even when it never terminates
-- statement:
--   Even if Howard's policy improvement algorithm runs forever without ever finding a
--   non-improvable decision rule, the sequence of values it generates is monotonically increasing and
--   still converges to the true optimal value $J_\infty$, provided either some iterate's value is
--   already non-negative or the model is contracting — a safety net that makes the algorithm useful
--   even without a finite termination guarantee.
--
--   **Moderation note.** The draft assumed only a monotone sequence of decision rules with a limit and concluded that the limit is $J_\infty$, which is false (a constant non-optimal $f$ with $J_f\ge 0$ satisfies the hypotheses). The sequence is now the one Howard's algorithm generates, $f_{k+1}$ a maximizer of $J_{f_k}$ (`hstep`); the monotonicity $J_{f_k}\ge J_{f_{k-1}}$ is a conclusion, and the two cases carry Theorem 7.5.1(b)/(c)'s conditions $T:\mathbb B\to\mathbb B$ resp. $T:\mathbb B_b\to\mathbb B_b$.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 213, Corollary 7.5.3

import Mathlib
import Definitions.Def_MDPFinance_LPDuality_Model
import Definitions.Def_MDPFinance_LPDuality_Value
import Definitions.Def_MDPFinance_LPDuality_Bounding

open MeasureTheory ProbabilityTheory Filter Topology

namespace MDPFinance.LPDuality

/-- Corollary 7.5.3 (Bäuerle–Rieder, p. 213, PDF 224). Let the assumptions of Theorem 7.5.1 be
satisfied. In case the algorithm does not stop, it generates a sequence of decision rules `(f_k)`
with `J_{f_k} \ge J_{f_{k-1}}`. If either `J_{f_k} \ge 0` for some `k` or the Markov Decision
Model is contracting, then it holds `\lim_k J_{f_k} = J_\infty`. The sequence is the one the
algorithm generates: `f_{k+1}` is a maximizer of `J_{f_k}` (step 3, `hstep`); the monotonicity
`J_{f_k} ≥ J_{f_{k-1}}` is then a conclusion. The two cases carry Theorem 7.5.1(b)/(c)'s standing
conditions `T : IB → IB` resp. `T : IB_b → IB_b`, and (A) is `hA`. -/
theorem corollary_7_5_3 {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] (M : MarkovDecisionModel E A)
    (hA : IntegrabilityAssumptionA M)
    (hC : ∀ x, Tendsto (fun n => (Tcirc M)^[n] (delta M) x) atTop (𝓝 (0 : EReal)))
    (fs : ℕ → E → A) (hfs : ∀ k, IsDecisionRuleOf M (fs k))
    (hstep : ∀ k, IsMaximizerOf M (fun y => Jinfpi M M.r (fun _ => fs k) y) (fs (k + 1))) :
    (∀ k x, Jinfpi M M.r (fun _ => fs k) x ≤ Jinfpi M M.r (fun _ => fs (k + 1)) x) ∧
      ((((∃ k, ∀ x, 0 ≤ Jinfpi M M.r (fun _ => fs k) x) ∧ (∀ v ∈ IB M, T M v ∈ IB M)) ∨
        (∃ b : E → ℝ, ∃ cr αb : ℝ, IsBoundingFunction M b cr αb ∧ M.β * αb < 1 ∧
          ∀ v ∈ IBb b, T' M v ∈ IBb b)) →
        ∀ x, Tendsto (fun k => Jinfpi M M.r (fun _ => fs k) x) atTop (𝓝 (Jinf M x))) := by sorry

end MDPFinance.LPDuality
