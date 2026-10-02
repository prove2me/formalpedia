-- Prove2me | Theorems.Thm_MDPFinance_LPDuality_theorem_7_4_5
-- name    : MDPFinance.LPDuality.theorem_7_4_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:52:52.963603+00:00
-- url     : https://prove2.me/theorems/797c1c22-ab57-44a4-89d7-6f9431a6ae4c
-- title:
--   Theorem 7.4.5 — a three-way optimality characterization for positive models
-- statement:
--   For a positive Markov Decision Model, a stationary policy's optimality, superharmonicity of its
--   value, and being a genuine fixed point of $T$ all coincide — a clean three-way equivalence not
--   available in general (chunk `07a`'s Example 7.2.4 already showed a maximizer of $J_\infty$ need
--   not give an optimal policy without further structure; Example 7.4.4, in this same section, shows
--   the positive-model analogue can also fail *without* assuming $(C^-)$-style superharmonicity is
--   achieved by *some* stationary policy at all).
--
--   **Moderation note.** Under the section's standing Integrability Assumption (A), $\varepsilon<\infty$ (`hAneg`), without which the extended-real stage values can be $\infty-\infty$; Lemma 7.4.1(a) is for $\pi\in F^\infty$.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 211, Theorem 7.4.5

import Mathlib
import Definitions.Def_MDPFinance_LPDuality_Model
import Definitions.Def_MDPFinance_LPDuality_Value

open MeasureTheory ProbabilityTheory Filter Topology List

namespace MDPFinance.LPDuality

/-- Theorem 7.4.5 (Bäuerle–Rieder, p. 211, PDF 222). Assume `(C^-)` and let `f \in F`. The
following statements are equivalent: (i) `f^\infty` is optimal. (ii) `J_f` is an
`r`-superharmonic function. (iii) `J_f` is a fixed point of `T`, i.e. `J_f = TJ_f`. -/
theorem theorem_7_4_5 {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] (M : MarkovDecisionModel E A)
    (hAneg : IntegrabilityAssumptionAneg M)
    (hCneg : ∀ x, Tendsto (fun n => (Tcirc M)^[n] (epsilon M) x) atTop (𝓝 (0 : EReal)))
    (f : E → A) (hf : IsDecisionRuleOf M f) :
    TFAE [∀ x, Jinfpi M M.r (fun _ => f) x = Jinf M x,
      ∀ x, T M (fun y => Jinfpi M M.r (fun _ => f) y) x ≤ Jinfpi M M.r (fun _ => f) x,
      ∀ x, T M (fun y => Jinfpi M M.r (fun _ => f) y) x = Jinfpi M M.r (fun _ => f) x] := by sorry

end MDPFinance.LPDuality
