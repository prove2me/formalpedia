-- Prove2me | Theorems.Thm_MDPFinance_Contracting_theorem_7_1_6
-- name    : MDPFinance.Contracting.theorem_7_1_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:45:52.104442+00:00
-- url     : https://prove2.me/theorems/417f47d1-e347-414d-a4cb-c4ae9f8e7cff
-- title:
--   Theorem 7.1.6 (Reward Iteration) — basic operator identities for infinite-horizon policies
-- statement:
--   For a policy $\pi = (f,\sigma)$ with first-stage rule $f$ and tail $\sigma \in F^\infty$, the
--   infinite-horizon value splits exactly as the one-stage operator would suggest: $J_\infty^\pi =
--   T_fJ_\infty^\sigma$. For a *stationary* policy $f^\infty := (f,f,\dots)$, its value $J_f :=
--   J_\infty^{f^\infty}$ belongs to the standing regularity class $IB$ and is a genuine fixed point
--   of $T_f$: $J_f = T_fJ_f$. This is the infinite-horizon reward iteration, the direct analogue of
--   chunk `02a`'s finite-horizon Theorem 2.3.4, and the first place a *fixed-point* characterization
--   of value appears in this chapter.
--
--   **Moderation note.** $\sigma\in F^\infty$ is a policy (`hσ`), and the chapter's standing Integrability Assumption (A) is a hypothesis (`hA`).
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 199, Theorem 7.1.6

import Mathlib
import Definitions.Def_MDPFinance_Contracting_Model
import Definitions.Def_MDPFinance_Contracting_Value

open MeasureTheory ProbabilityTheory Filter Topology

namespace MDPFinance.Contracting

/-- Theorem 7.1.6 (Reward Iteration) (Bäuerle–Rieder, p. 199, PDF 210 (corrected from BRIEF.md's "p. 198"; the printed footer at PDF 210 reads 199)). Assume (C) and let
`\pi = (f,\sigma) \in F \times F^\infty`. Then it holds: a) `J_\infty^\pi = T_fJ_\infty^\sigma`.
b) `J_f \in IB` and `J_f = T_fJ_f`, where `J_f := J_\infty^{f^\infty}`. `σ ∈ F^∞` is a policy; the
chapter's standing Integrability Assumption (A) is `hA`. -/
theorem theorem_7_1_6 {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] (M : MarkovDecisionModel E A)
    (hA : IntegrabilityAssumptionA M)
    (hC : ∀ x, Tendsto (fun n => (Tcirc M)^[n] (delta M) x) atTop (𝓝 (0 : EReal)))
    (f : E → A) (hf : IsDecisionRuleOf M f) (σ : ℕ → E → A) (hσ : IsPolicyOf M σ) :
    (∀ x, Jinfpi M M.r (consPolicy f σ) x = Tf M f (fun y => Jinfpi M M.r σ y) x) ∧
      (fun x => Jinfpi M M.r (fun _ => f) x) ∈ IB M ∧
      (∀ x, Jinfpi M M.r (fun _ => f) x = Tf M f (fun y => Jinfpi M M.r (fun _ => f) y) x) := by sorry

end MDPFinance.Contracting
