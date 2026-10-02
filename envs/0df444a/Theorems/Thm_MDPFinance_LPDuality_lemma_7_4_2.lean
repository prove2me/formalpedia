-- Prove2me | Theorems.Thm_MDPFinance_LPDuality_lemma_7_4_2
-- name    : MDPFinance.LPDuality.lemma_7_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:52:43.586977+00:00
-- url     : https://prove2.me/theorems/b9053c1a-2967-4788-95b8-c0d61c48d547
-- title:
--   Lemma 7.4.2 — operator convergence for positive models
-- statement:
--   Under the positive-model convergence assumption $(C^-)$, the operators $L$ and $T_f$ commute
--   with the limit of the finite-horizon values, exactly as chunk `07a`'s Lemma 7.1.5 established for
--   the general theory — and, as a direct corollary, $J_f$ (the value of a stationary policy) is a
--   genuine fixed point of $T_f$.
--
--   **Moderation note.** Under the section's standing Integrability Assumption (A), $\varepsilon<\infty$ (`hAneg`), without which the extended-real stage values can be $\infty-\infty$; Lemma 7.4.1(a) is for $\pi\in F^\infty$.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 209, Lemma 7.4.2

import Mathlib
import Definitions.Def_MDPFinance_LPDuality_Model
import Definitions.Def_MDPFinance_LPDuality_Value

open MeasureTheory ProbabilityTheory Filter Topology

namespace MDPFinance.LPDuality

/-- Lemma 7.4.2 (Bäuerle–Rieder, p. 209, PDF 220). Assume `(C^-)` (`\lim_n T_\circ^n\varepsilon(x)
= 0`) and let `f \in F`. Then it holds: a) `\lim_n LJ_n(x,a) = LJ(x,a)`, `(x,a) \in D`. b)
`\lim_n T_fJ_n(x) = T_fJ(x)`, `x \in E`. c) `J_f = T_fJ_f`. -/
theorem lemma_7_4_2 {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] (M : MarkovDecisionModel E A)
    (hAneg : IntegrabilityAssumptionAneg M)
    (hCneg : ∀ x, Tendsto (fun n => (Tcirc M)^[n] (epsilon M) x) atTop (𝓝 (0 : EReal)))
    (f : E → A) (hf : IsDecisionRuleOf M f) :
    (∀ xa ∈ M.D, Tendsto (fun n => L M (Jn M M.r n) xa) atTop (𝓝 (L M (Jlim M) xa))) ∧
      (∀ x, Tendsto (fun n => Tf M f (Jn M M.r n) x) atTop (𝓝 (Tf M f (Jlim M) x))) ∧
      (∀ x, Jinfpi M M.r (fun _ => f) x = Tf M f (fun y => Jinfpi M M.r (fun _ => f) y) x) := by sorry

end MDPFinance.LPDuality
