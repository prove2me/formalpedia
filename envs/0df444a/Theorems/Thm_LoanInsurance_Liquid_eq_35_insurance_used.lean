-- Prove2me | Theorems.Thm_LoanInsurance_Liquid_eq_35_insurance_used
-- name    : LoanInsurance.Liquid.eq_35_insurance_used
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:33:21.321963+00:00
-- url     : https://prove2.me/theorems/72629cf0-4891-4667-b7c6-ef1f5de06ad7
-- title:
--   (34)–(35), p. 42 (PDF 46) — (33) at η* equals p*_U exactly at m = m*, increases in m, and m* > 0 iff (35)
-- statement:
--   Under the standing assumptions, suppose $\psi>\underline\psi=\lambda\mu/(\lambda\mu+\kappa(1-\mu))$ and $F(\eta^*)<1$, where $\eta^*$ is the threshold of Proposition 2. Write $p^{(33)}(\eta,m)$ for the uninsured-loan price (33). Then
--
--   1. $p^{(33)}(\eta^*,m^*)=p^*_U$, i.e. $m^*$ solves (34);
--   2. $m^*<1$;
--   3. $m\mapsto p^{(33)}(\eta^*,m)$ is strictly increasing on $[0,1]$;
--   4. insurance is used, $m^*>0$, if and only if condition (35) holds:
--   $$\nu\frac{\psi F(\eta^*)+\mu(1-F(\eta^*))}{\nu+(1-\nu)[(1-\psi)F(\eta^*)+(1-\mu)(1-F(\eta^*))]}<\frac{\nu\lambda\mu}{\nu\lambda+(1-\nu)(1-\mu)}.$$
--
--   Condition (35) says that, without insurance, the uninsured price at threshold $\eta^*$ would fall short of the price $p^*_U$ at which high-cost lenders are indifferent about insurance.
--
--   **Formalization Note** $F(\eta^*)<1$ is the regime in which the share $m^*$ is well defined (its formula divides by $1-F(\eta^*)$).
-- source:
--   Ahnert & Kuncl, Loan Insurance, Market Liquidity, and Lending Standards, Bank of Canada Staff Working Paper 2019-47 (last updated August 2020), p. 42 (PDF 46), (34)–(35); (33) p. 41 (PDF 45)

import Mathlib
import Definitions.Def_LoanInsurance_Liquid_Model

namespace LoanInsurance.Liquid

/-- (34)–(35) (p. 42): at the threshold `η*`, the price (33) equals `p*_U` at `m = m*`, it is
strictly increasing in `m` on `[0, 1]`, `m* < 1`, and insurance is used (`m* > 0`) exactly
when (35) holds. -/
theorem eq_35_insurance_used (P : Params) (hP : P.Standing) (hψ : P.psiUnder < P.ψ)
    (hF : P.F P.etaStar < 1) :
    P.price33 P.etaStar P.mStar = P.pUStar ∧ P.mStar < 1 ∧
      StrictMonoOn (P.price33 P.etaStar) (Set.Icc 0 1) ∧
      (0 < P.mStar ↔ P.Cond35) := by sorry

end LoanInsurance.Liquid
