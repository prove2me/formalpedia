-- Prove2me | Theorems.Thm_LoanInsurance_Liquid_eq_5_threshold
-- name    : LoanInsurance.Liquid.eq_5_threshold
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:33:16.311985+00:00
-- url     : https://prove2.me/theorems/26c273ad-1670-49b4-9fd7-ee4cee5c7f69
-- title:
--   (5), p. 11 (PDF 15), as used in B.3, p. 41 — the screening threshold is η = (1 − ν)(ψ − µ)(A − p_U), hence η = η* when insurance is used
-- statement:
--   Under the standing assumptions, take a liquid equilibrium with loan insurance (Definition 1) with an interior screening threshold $0<\eta<\bar\eta$ in which not all high-cost lenders insure, $m<1$. Then the marginal lender is indifferent between screening and not screening (without insuring), so
--   $$\eta=(1-\nu)(\psi-\mu)(A-p_U).\qquad(5)$$
--   If moreover insurance is used, $m>0$, then
--   $$\eta=\eta^*=\frac{(1-\nu)(1-\mu)(\psi-\mu)\kappa A}{\nu\lambda+(1-\nu)(1-\mu)},\qquad \kappa=\nu\lambda+1-\nu.$$
--
--   The screening benefit accrues only without a liquidity shock, where it is the higher chance of keeping a good loan instead of selling a lemon at $p_U$.
-- source:
--   Ahnert & Kuncl, Loan Insurance, Market Liquidity, and Lending Standards, Bank of Canada Staff Working Paper 2019-47 (last updated August 2020), p. 11 (PDF 15), (5); Appendix B.3, p. 41 (PDF 45)

import Mathlib
import Definitions.Def_LoanInsurance_Liquid_Model

namespace LoanInsurance.Liquid

/-- (5) (p. 11), as used in Appendix B.3 (p. 41): in an interior liquid equilibrium in which some
high-cost lenders do not insure, the screening threshold is `η = (1 − ν)(ψ − μ)(A − p_U)`; if
insurance is used, it equals `η*` of Proposition 2. -/
theorem eq_5_threshold (P : Params) (hP : P.Standing) (e : Profile) (he : P.LiquidEq e)
    (hm1 : e.m < 1) (heta0 : 0 < e.eta) (heta1 : e.eta < P.etaBar) :
    e.eta = (1 - P.ν) * (P.ψ - P.μ) * (P.A - e.pU) ∧
      (0 < e.m → e.eta = P.etaStar) := by sorry

end LoanInsurance.Liquid
