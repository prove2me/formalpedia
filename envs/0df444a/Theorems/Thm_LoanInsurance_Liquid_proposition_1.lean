-- Prove2me | Theorems.Thm_LoanInsurance_Liquid_proposition_1
-- name    : LoanInsurance.Liquid.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:33:32.266573+00:00
-- url     : https://prove2.me/theorems/9df2212b-544b-4799-8533-0b54e30dca7e
-- title:
--   Proposition 1 (liquid case), p. 13 (PDF 17) — low-cost lenders do not insure; fee k* = (1 − µ)A and p*_I = π* = µA; m* < 1 for ψ > ψ̲
-- statement:
--   Under the standing assumptions, let a liquid equilibrium with loan insurance (Definition 1) have a positive screening threshold $\eta>0$. Then
--
--   1. low-cost lenders (those who screen) do not insure: the share $m_L$ of screeners who insure is $0$;
--   2. if a positive mass of loans is insured, $m(1-F(\eta))>0$, the insurance fee and the price of insured loans are
--   $$k^*=(1-\mu)A,\qquad \pi^*=p^*_I=\mu A.$$
--   3. if screening is productive enough, $\psi>\underline\psi=\lambda\mu/(\lambda\mu+\kappa(1-\mu))$, and some lenders are high-cost, $\eta<\bar\eta$, then the share of high-cost lenders who insure is $m<1$.
--
--   Insurance therefore reveals that the lender did not screen, and insured loans trade at the value of an average unscreened loan.
--
--   **Formalization Note** That lenders below the threshold screen is built into the threshold profile. The fee claim needs an insured mass: if nobody insures, every fee breaks even. Item 3 is the liquid half of the last sentence of Proposition 1 ($m^*\in[0,1)$ for $\psi>\underline\psi$); it needs $\eta<\bar\eta$, since with no high-cost lenders their share $m$ is not determined. The illiquid half ($m^*=1$ in an illiquid equilibrium) is not formalized.
-- source:
--   Ahnert & Kuncl, Loan Insurance, Market Liquidity, and Lending Standards, Bank of Canada Staff Working Paper 2019-47 (last updated August 2020), p. 13 (PDF 17), Proposition 1 (liquid case), (7); proof Appendix B.2, p. 41 (PDF 45)

import Mathlib
import Definitions.Def_LoanInsurance_Liquid_Model

namespace LoanInsurance.Liquid

/-- Proposition 1 (p. 13), liquid case: in a liquid equilibrium with a positive screening
threshold, low-cost lenders do not insure; when a positive mass of loans is insured the fee is
`k* = (1 − μ)A` and the price of insured loans is `p*_I = π* = μA`; and for `ψ > ψ̲`, when the
class of high-cost lenders is nonempty (`η < η̄`), their share who insure is `m < 1`. -/
theorem proposition_1 (P : Params) (hP : P.Standing) (e : Profile) (he : P.LiquidEq e)
    (heta : 0 < e.eta) :
    e.mL = 0 ∧
      (0 < e.m * (1 - P.F e.eta) → e.k = (1 - P.μ) * P.A ∧ e.pI = P.μ * P.A) ∧
      (P.psiUnder < P.ψ → e.eta < P.etaBar → e.m < 1) := by sorry

end LoanInsurance.Liquid
