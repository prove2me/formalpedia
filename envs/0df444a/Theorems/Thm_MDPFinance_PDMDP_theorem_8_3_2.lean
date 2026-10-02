-- Prove2me | Theorems.Thm_MDPFinance_PDMDP_theorem_8_3_2
-- name    : MDPFinance.PDMDP.theorem_8_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:09:37.494865+00:00
-- url     : https://prove2.me/theorems/26b4c85a-65ce-4d8c-b871-7d17ba4addb1
-- title:
--   Theorem 8.3.2 — value equality, finite-horizon chain
-- statement:
--   The finite-horizon analogue of Theorem 8.2.1: for a Markov policy $\pi=(f_n)$ (now depending on both the jump time and the post-jump state), the continuous-time expected reward $V^\pi(t_0,x)$ of any realization of the finite-horizon chain equals the reward-to-go $J_\infty(f_n)(t_0,x)$ of the discrete-time model embedded on the extended state space $E'=[0,T]\times E$. As with Theorem 8.2.1, the book's further remark "Moreover, $V=J_\infty$" is adopted operationally for `theorem_8_3_3`'s own use of $V$.
--
--   **Formalization Note.** Since the chain's flow is trivial, its realization (`MDChainRealizationFinite`) needs no ODE/flow data, only the jump-time/post-jump-state process — genuinely simpler than `PDMDPRealization`, matching this chapter's own remark that the chain is a different, simpler object than the general Piecewise Deterministic model.
--
--   **Moderation note.** As for Theorem 8.2.1, but for the finite-horizon chain: the draft asserted the identity for every map and with real junk values. Now under the Integrability Assumption and for a jointly measurable policy, every realization has `V_π(t_0,x) = J_{∞π}(t_0,x)` for `t_0 ∈ [0,T]`.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 259, PDF 270, Theorem 8.3.2

import Mathlib
import Definitions.Def_MDPFinance_PDMDP_Model
import Definitions.Def_MDPFinance_PDMDP_Chain
import Definitions.Def_MDPFinance_PDMDP_ChainProcess

open MeasureTheory ProbabilityTheory

namespace MDPFinance.PDMDP

variable {E U : Type*} [MeasurableSpace E] [Countable E] [MeasurableSpace U]

/-- Theorem 8.3.2 (Bäuerle–Rieder, p. 259, PDF 270): for a Markov policy `π = (f_n)` (measurable
`f_n : [0,T] × E → A`) and `(t_0,x) ∈ E' = [0,T] × E`, the continuous-time expected reward
`V^π(t_0,x)` of any realization of the finite-horizon chain equals the reward-to-go
`J_∞(f)(t_0,x)` of the embedded discrete-time model, under the standing Integrability Assumption
(A). "Moreover, `V = J_∞`" is the supremum over policies of this identity, the operational reading
of `V` (`Vinf`) in Theorem 8.3.3. -/
theorem theorem_8_3_2 {Ω : Type*} [MeasurableSpace Ω] (Ch : MDChainFinite E U)
    (hA : IntegrabilityAssumptionChainFinite Ch)
    (f : ℕ → ℝ → E → ControlFn U) (hf : IsChainPolicyFinite f) (t0 : ℝ) (ht0 : 0 ≤ t0)
    (ht0Th : t0 ≤ Ch.Th) (x : E) (R : MDChainRealizationFinite Ω Ch f t0 x) :
    R.Vpi = Ch.Jinf f t0 x := by sorry

end MDPFinance.PDMDP
