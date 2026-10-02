-- Prove2me | Theorems.Thm_MDPFinance_LPDuality_theorem_7_5_1
-- name    : MDPFinance.LPDuality.theorem_7_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:53:06.959536+00:00
-- url     : https://prove2.me/theorems/dd72b40f-f39e-49ca-93ec-243ecbae8082
-- title:
--   Theorem 7.5.1 (Howard's Policy Improvement) — a locally-improving decision rule improves value
-- statement:
--   Howard's policy improvement algorithm computes an optimal policy by repeatedly replacing a
--   decision rule with a strict pointwise improvement wherever one exists. This theorem justifies
--   each step: if $D(x,f)$ (states where switching action strictly beats $f$) is used to build a new
--   rule $h$, then $h$'s value dominates $f$'s value everywhere and strictly improves it wherever the
--   switch was made (part a). Once no improvement exists anywhere ($D(x,f) = \emptyset$ for all $x$),
--   the current policy is already optimal — under either a general regularity condition on $T$ (part
--   b) or, more simply, whenever the model is contracting (part c).
--
--   **Moderation note.** The chapter's standing Integrability Assumption (A) is a hypothesis (`hA`).
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 212, Theorem 7.5.1

import Mathlib
import Definitions.Def_MDPFinance_LPDuality_Model
import Definitions.Def_MDPFinance_LPDuality_Value
import Definitions.Def_MDPFinance_LPDuality_Bounding

open MeasureTheory ProbabilityTheory Filter Topology

namespace MDPFinance.LPDuality

/-- Theorem 7.5.1 (Bäuerle–Rieder, p. 212, PDF 223). Let (C) be satisfied. For a decision rule
`f \in F` denote `D(x,f) := \{a \in D(x) \mid LJ_f(x,a) > J_f(x)\}`. Then it holds: a) If for
some measurable `E_0 \subset E` we define a decision rule `h` by `h(x) \in D(x,f)` for `x \in
E_0`, `h(x) = f(x)` for `x \notin E_0`, then `J_h \ge J_f` and `J_h(x) > J_f(x)` for `x \in E_0`
(`h` is called an improvement of `f`). b) If `D(x,f) = \emptyset` for all `x \in E`, `J_f \ge 0`
and `T : IB \to IB`, then `J_f = J_\infty`. c) Let `b` be a bounding function, `\beta\alpha_b <
1` and `T : IB_b \to IB_b`. If `D(x,f) = \emptyset` for all `x \in E`, then `J_f = J_\infty`.
`h`'s existence on `E_0` (choosing a value in the possibly multi-valued `D(x,f)`) is taken as a
hypothesis (`hh_sel`), the measurable-selection step the book's own construction needs. The
chapter's standing Integrability Assumption (A) is `hA`. -/
theorem theorem_7_5_1 {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] (M : MarkovDecisionModel E A)
    (hA : IntegrabilityAssumptionA M)
    (hC : ∀ x, Tendsto (fun n => (Tcirc M)^[n] (delta M) x) atTop (𝓝 (0 : EReal)))
    (f : E → A) (hf : IsDecisionRuleOf M f)
    (Dxf : E → Set A) (hDxf : ∀ x, Dxf x = {a ∈ M.Dx x | Jinfpi M M.r (fun _ => f) x <
      L M (fun y => Jinfpi M M.r (fun _ => f) y) (x, a)}) :
    (∀ E0 : Set E, MeasurableSet E0 → ∀ h : E → A, IsDecisionRuleOf M h →
        (∀ x ∈ E0, h x ∈ Dxf x) → (∀ x ∉ E0, h x = f x) →
        (∀ x, Jinfpi M M.r (fun _ => f) x ≤ Jinfpi M M.r (fun _ => h) x) ∧
          ∀ x ∈ E0, Jinfpi M M.r (fun _ => f) x < Jinfpi M M.r (fun _ => h) x) ∧
      ((∀ x, Dxf x = ∅) → (∀ x, 0 ≤ Jinfpi M M.r (fun _ => f) x) →
        (∀ v ∈ IB M, T M v ∈ IB M) →
        ∀ x, Jinfpi M M.r (fun _ => f) x = Jinf M x) ∧
      (∀ b : E → ℝ, ∀ cr αb : ℝ, IsBoundingFunction M b cr αb → M.β * αb < 1 →
        (∀ v ∈ IBb b, T' M v ∈ IBb b) → (∀ x, Dxf x = ∅) →
        ∀ x, Jinfpi M M.r (fun _ => f) x = Jinf M x) := by sorry

end MDPFinance.LPDuality
