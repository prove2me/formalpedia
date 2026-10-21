-- Prove2me | Theorems.Thm_LoanInsurance_Liquid_eq_8_indifference
-- name    : LoanInsurance.Liquid.eq_8_indifference
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:33:15.20054+00:00
-- url     : https://prove2.me/theorems/0efd8d60-0ce7-49a4-a3e8-d76c95c6114f
-- title:
--   (8), p. 14 (PDF 18), and B.3, p. 41 — high-cost lenders' indifference about insurance pins down p*_U = νλµA/(νλ + (1 − ν)(1 − µ))
-- statement:
--   Under the standing assumptions, take a liquid equilibrium with loan insurance (Definition 1) in which high-cost lenders are indifferent about insurance, $0<m<1$, and the screening threshold is below the top of the cost support, $\eta<\bar\eta$. Then $p_I=\mu A$, the indifference condition
--   $$\nu\lambda\,(p^*_I-p^*_U)=(1-\nu)(1-\mu)\,p^*_U\qquad(8)$$
--   holds, and consequently
--   $$p^*_U=\frac{\nu\lambda\mu A}{\nu\lambda+(1-\nu)(1-\mu)}.$$
--
--   The left side of (8) is the benefit of insurance (a higher sale price after a liquidity shock), the right side its cost (the lost option to sell a lemon when no shock arrives).
--
--   **Formalization Note** $\eta<\bar\eta$ makes the set of high-cost lenders nonempty, so their indifference is a property of the equilibrium.
-- source:
--   Ahnert & Kuncl, Loan Insurance, Market Liquidity, and Lending Standards, Bank of Canada Staff Working Paper 2019-47 (last updated August 2020), p. 14 (PDF 18), (8); Appendix B.3, p. 41 (PDF 45), first sentence

import Mathlib
import Definitions.Def_LoanInsurance_Liquid_Model

namespace LoanInsurance.Liquid

/-- (8) (p. 14) and Appendix B.3 (p. 41): in a liquid equilibrium in which high-cost lenders are
indifferent about insurance, `p_I = μA`, the indifference condition (8) holds, and it pins down
`p*_U = νλμA/(νλ + (1 − ν)(1 − μ))`. -/
theorem eq_8_indifference (P : Params) (hP : P.Standing) (e : Profile) (he : P.LiquidEq e)
    (hm0 : 0 < e.m) (hm1 : e.m < 1) (heta : e.eta < P.etaBar) :
    e.pI = P.μ * P.A ∧
      P.ν * P.lam * (e.pI - e.pU) = (1 - P.ν) * (1 - P.μ) * e.pU ∧
      e.pU = P.pUStar := by sorry

end LoanInsurance.Liquid
