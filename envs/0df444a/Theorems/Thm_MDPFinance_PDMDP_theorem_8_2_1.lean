-- Prove2me | Theorems.Thm_MDPFinance_PDMDP_theorem_8_2_1
-- name    : MDPFinance.PDMDP.theorem_8_2_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:08:53.125504+00:00
-- url     : https://prove2.me/theorems/63c149ab-d416-4a79-80da-7b18919f789e
-- title:
--   Theorem 8.2.1 — value equality between the continuous-time process and its discrete-time embedding
-- statement:
--   For a Markov policy $\pi=(f_n)$, this theorem identifies the continuous-time expected discounted reward $V^\pi(x)$ of *any* realization of the Piecewise Deterministic Markov Decision Process with the reward-to-go $J_\infty(f_n)(x)$ of the discrete-time model obtained by embedding at the jump times. This is the technical heart of the whole chapter: it is what lets every later existence/verification result be proved by discrete-time dynamic-programming methods (Chapter 7's machinery) rather than continuous-time stochastic control. The book's further remark "Moreover, $V=J_\infty$" — the identity's supremum over all policies — is adopted as this chunk's operational reading of $V_\infty$ in every later item that mentions it (`theorem_8_2_7`, `theorem_8_2_8`), since no separate continuous-time construction is needed once this correspondence is available.
--
--   **Formalization Note.** `R : PDMDPRealization Ω Mk f x` is universally quantified: the identity is asserted for *any* probability-space realization satisfying the model's own defining conditional law, not for one specific canonical construction (whose existence the book itself only asserts, citing general marked-point-process theory, rather than constructs).
--
--   **Moderation note.** The draft asserted `V_π(x) = J_∞(x)` for *every* function `f` (no policy admissibility, no Integrability Assumption, real-valued junk on both sides). Now the theorem assumes (A) for the embedded model and a measurable policy `f ∈ F^∞`, and states that every realization of `π = (f_n)` has `V_π(x) = J_{∞π}(x)` in `[-∞,∞]`, with the induced value equal to the embedded model's.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 248, PDF 259, Theorem 8.2.1

import Mathlib
import Definitions.Def_MDPFinance_PDMDP_Model
import Definitions.Def_MDPFinance_PDMDP_Embedding
import Definitions.Def_MDPFinance_PDMDP_Process

open MeasureTheory ProbabilityTheory

namespace MDPFinance.PDMDP

variable {E U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [MeasurableSpace U] [TopologicalSpace U]

/-- Theorem 8.2.1 (Bäuerle–Rieder, p. 248, PDF 259): for a Markov policy `π = (f_n)` (measurable
decision rules), the continuous-time expected discounted reward `V^π(x)` of any realization of
the Piecewise Deterministic Markov Decision Process equals the reward-to-go `J_∞(f)(x)` of the
embedded discrete-time model, under the standing Integrability Assumption (A). The book's
"Moreover, `V = J_∞`" is the supremum over policies of this identity and is the operational
reading of `V_∞` in this chunk (`JinfSup`). -/
theorem theorem_8_2_1 {Ω : Type*} [MeasurableSpace Ω] (Mk : PDMDPModel E U)
    (Emb : EmbeddedKernel Mk) (hA : IntegrabilityAssumptionPD Mk Emb)
    (f : ℕ → E → ControlFn U) (hf : IsPDPolicy f) (x : E)
    (R : PDMDPRealization Ω Mk f x) :
    R.Vpi = JinfEmbed Mk Emb f x := by sorry

end MDPFinance.PDMDP
