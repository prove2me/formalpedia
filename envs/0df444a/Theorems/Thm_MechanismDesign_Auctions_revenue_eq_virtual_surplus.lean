-- Prove2me | Theorems.Thm_MechanismDesign_Auctions_revenue_eq_virtual_surplus
-- name    : MechanismDesign.Auctions.revenue_eq_virtual_surplus
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T23:45:02.228686+00:00
-- url     : https://prove2.me/theorems/bc97ec44-afae-44fe-9c25-51378f8971e5
-- title:
--   Eqs. (3.4)–(3.5) -- expected revenue equals expected virtual surplus
-- statement:
--   Let $(q,t)$ be a well-defined, incentive-compatible direct mechanism in the single-unit auction environment whose interim payments satisfy Eq. (3.3), i.e. $T_i(\underline\theta) = \underline\theta\,Q_i(\underline\theta)$ for every buyer $i$. Let $\psi_i(\theta_i) = \theta_i - (1 - F_i(\theta_i))/f_i(\theta_i)$ be buyer $i$'s virtual valuation.
--
--   **Eqs. (3.4)–(3.5).** The seller's expected revenue equals
--   $$\sum_{i \in I} \int_{\underline\theta}^{\bar\theta} Q_i(\theta_i)\,\psi_i(\theta_i)\,f_i(\theta_i)\,d\theta_i \;=\; \sum_{i\in I} \int_\Theta q_i(\theta)\,\psi_i(\theta_i)\,f(\theta)\,d\theta.$$
--
--   This identity turns revenue maximization into pointwise maximization of the virtual surplus $\sum_i q_i(\theta)\psi_i(\theta_i)$, which is how Myerson's allocation rule arises.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.40, Eqs. (3.4)–(3.5)

import Mathlib
import Definitions.Def_MechanismDesign_Auctions_Model

open MeasureTheory

namespace MechanismDesign.Auctions

/-- Eqs. (3.4)–(3.5), p.40: for an incentive-compatible direct mechanism whose payments satisfy
(3.3), i.e. `T_i(θ̲) = θ̲ Q_i(θ̲)` for all `i`, the seller's expected revenue equals
`∑_i ∫_{θ̲}^{θ̄} Q_i(θ_i) ψ_i(θ_i) f_i(θ_i) dθ_i = ∑_i ∫_Θ q_i(θ) ψ_i(θ_i) f(θ) dθ`. -/
theorem revenue_eq_virtual_surplus {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Environment ι}
    (m : DirectMechanism E) (hwd : m.WellDefined) (hIC : m.IsIC)
    (hlow : ∀ i, m.interimT i E.lo = E.lo * m.interimQ i E.lo) :
    m.revenue = ∑ i, ∫ x in E.lo..E.hi, m.interimQ i x * E.virtualValue i x * E.f i x ∧
    m.revenue = ∑ i, ∫ θ, m.q i θ * E.virtualValue i (θ i) ∂E.prior := by sorry

end MechanismDesign.Auctions
