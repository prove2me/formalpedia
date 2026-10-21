-- Prove2me | Theorems.Thm_LoanInsurance_Liquid_eq_38_price_increasing
-- name    : LoanInsurance.Liquid.eq_38_price_increasing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:33:25.799837+00:00
-- url     : https://prove2.me/theorems/4164bd88-db07-4dd4-908e-da0e941b6aad
-- title:
--   (38), pp. 42–43 (PDF 46–47) — more loan insurance raises the price of uninsured loans and lowers the screening threshold
-- statement:
--   Under the standing assumptions, let $0\le m<m'\le1$ be two shares of high-cost lenders who insure. Suppose $(\eta,p)$ solves the screening condition (5) together with the price (33) at share $m$,
--   $$\eta=(1-\nu)(\psi-\mu)(A-p),\qquad p=p^{(33)}(\eta,m),$$
--   and $(\eta',p')$ solves the same system at share $m'$, with both thresholds interior, $0<\eta,\eta'<\bar\eta$. Then
--   $$p<p'\qquad\text{and}\qquad\eta'<\eta.$$
--
--   This is the comparative statics behind part 1 of Proposition 2: removing insured lemons from the uninsured market raises the uninsured price, which lowers the screening incentive.
--
--   **Formalization Note** The paper states (38) with derivatives along the equilibrium curve; here it is stated as a comparison of two solutions, which needs no differentiability of $F$. Interior thresholds are required because at $F(\eta)\in\{0,1\}$ the price (33) does not depend on $m$.
-- source:
--   Ahnert & Kuncl, Loan Insurance, Market Liquidity, and Lending Standards, Bank of Canada Staff Working Paper 2019-47 (last updated August 2020), pp. 42–43 (PDF 46–47), (38)

import Mathlib
import Definitions.Def_LoanInsurance_Liquid_Model

namespace LoanInsurance.Liquid

/-- (38) (pp. 42–43), without derivatives: for shares `0 ≤ m < m′ ≤ 1` of insuring high-cost
lenders, if `(η, p)` and `(η′, p′)` are interior solutions of the threshold equation (5) and the
price (33) at `m` and `m′`, then the price is higher and the threshold lower at `m′`. -/
theorem eq_38_price_increasing (P : Params) (hP : P.Standing) (m m' η p η' p' : ℝ)
    (hm : 0 ≤ m) (hmm' : m < m') (hm' : m' ≤ 1)
    (hη0 : 0 < η) (hη1 : η < P.etaBar) (hη'0 : 0 < η') (hη'1 : η' < P.etaBar)
    (h5 : η = (1 - P.ν) * (P.ψ - P.μ) * (P.A - p)) (h33 : p = P.price33 η m)
    (h5' : η' = (1 - P.ν) * (P.ψ - P.μ) * (P.A - p')) (h33' : p' = P.price33 η' m') :
    p < p' ∧ η' < η := by sorry

end LoanInsurance.Liquid
