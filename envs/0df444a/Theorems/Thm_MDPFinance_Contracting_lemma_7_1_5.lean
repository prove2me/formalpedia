-- Prove2me | Theorems.Thm_MDPFinance_Contracting_lemma_7_1_5
-- name    : MDPFinance.Contracting.lemma_7_1_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:45:36.374492+00:00
-- url     : https://prove2.me/theorems/a179b8ab-6959-4848-b268-657a97d5326e
-- title:
--   Lemma 7.1.5 — the L-operator commutes with the limit of the finite-horizon values
-- statement:
--   Under the Convergence Assumption (C), the one-stage operator $L$ (resp. $T_f$ for a fixed
--   decision rule $f$) commutes with taking the limit of the finite-horizon value functions: $\lim_n
--   LJ_n(x,a) = LJ(x,a)$ and $\lim_n T_fJ_n(x) = T_fJ_f(x)$. This is the technical bridge that lets
--   the finite-horizon reward-iteration machinery (chunk `02a`'s Theorem 2.3.4) be carried over to
--   the infinite-horizon limit value function $J$, yielding Theorem 7.1.6's reward iteration as a
--   corollary.
--
--   **Moderation note.** The chapter's standing Integrability Assumption (A), $\delta<\infty$, is a hypothesis (`hA`); it is not implied by the Convergence Assumption (C) as formalized (the tail $T_\circ^n\delta\to 0$ says nothing about $\delta$ itself), and the values are only the book's expectations under it.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 198, Lemma 7.1.5

import Mathlib
import Definitions.Def_MDPFinance_Contracting_Model
import Definitions.Def_MDPFinance_Contracting_Value

open MeasureTheory ProbabilityTheory Filter Topology

namespace MDPFinance.Contracting

/-- Lemma 7.1.5 (Bäuerle–Rieder, p. 198, PDF 209). Assume (C) (Convergence Assumption, p. 195:
`\lim_n T_\circ^n \delta(x) = 0` for all `x`; the chapter's standing Integrability Assumption (A),
`δ < ∞`, is `hA`) and let `f \in F`. Then it holds: a) `\lim_n
LJ_n(x,a) = LJ(x,a)` for all `(x,a) \in D`. b) `\lim_n T_fJ_n(x) = T_fJ(x)` for all `x \in E`. -/
theorem lemma_7_1_5 {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] (M : MarkovDecisionModel E A)
    (hA : IntegrabilityAssumptionA M)
    (hC : ∀ x, Tendsto (fun n => (Tcirc M)^[n] (delta M) x) atTop (𝓝 (0 : EReal)))
    (f : E → A) (hf : IsDecisionRuleOf M f) :
    (∀ xa ∈ M.D, Tendsto (fun n => L M (Jn M M.r n) xa) atTop (𝓝 (L M (Jlim M) xa))) ∧
      (∀ x, Tendsto (fun n => Tf M f (Jn M M.r n) x) atTop (𝓝 (Tf M f (Jlim M) x))) := by sorry

end MDPFinance.Contracting
