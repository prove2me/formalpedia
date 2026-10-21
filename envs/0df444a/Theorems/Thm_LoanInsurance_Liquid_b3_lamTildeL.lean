-- Prove2me | Theorems.Thm_LoanInsurance_Liquid_b3_lamTildeL
-- name    : LoanInsurance.Liquid.b3_lamTildeL
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:33:21.99558+00:00
-- url     : https://prove2.me/theorems/05048efc-a488-42f8-9282-77448d0e229c
-- title:
--   Appendix B.3, p. 41 (PDF 45) — p*_U satisfies (2) iff µνλ² − νλ − (1 − µ)(1 − ν) ≥ 0 iff λ ≥ λ̃_L
-- statement:
--   Under the standing assumptions, the price $p^*_U=\nu\lambda\mu A/(\nu\lambda+(1-\nu)(1-\mu))$ satisfies the liquidity condition (2), $\lambda p^*_U\ge A$, if and only if
--   $$\mu\nu\lambda^2-\nu\lambda-(1-\mu)(1-\nu)\ge0,$$
--   and this holds if and only if
--   $$\lambda\ge\tilde\lambda_L\equiv\frac1{2\mu}+\sqrt{\frac1{4\mu^2}+\frac{(1-\mu)(1-\nu)}{\mu\nu}}.$$
--
--   The bound $\tilde\lambda_L$ is the larger root of the quadratic; it is the existence condition on the shock size in Proposition 2.
-- source:
--   Ahnert & Kuncl, Loan Insurance, Market Liquidity, and Lending Standards, Bank of Canada Staff Working Paper 2019-47 (last updated August 2020), Appendix B.3, p. 41 (PDF 45), "Thus, a liquid equilibrium in which insurance is used exists if µνλ² − νλ − (1 − µ)(1 − ν) ≥ 0."; λ̃_L from Proposition 2, p. 15 (PDF 19)

import Mathlib
import Definitions.Def_LoanInsurance_Liquid_Model

namespace LoanInsurance.Liquid

/-- Appendix B.3 (p. 41): the price `p*_U` satisfies the liquidity condition (2) iff
`μνλ² − νλ − (1 − μ)(1 − ν) ≥ 0`, iff `λ ≥ λ̃_L`. -/
theorem b3_lamTildeL (P : Params) (hP : P.Standing) :
    (P.A ≤ P.lam * P.pUStar ↔
        0 ≤ P.μ * P.ν * P.lam ^ 2 - P.ν * P.lam - (1 - P.μ) * (1 - P.ν)) ∧
      (0 ≤ P.μ * P.ν * P.lam ^ 2 - P.ν * P.lam - (1 - P.μ) * (1 - P.ν) ↔
        P.lamTildeL ≤ P.lam) := by sorry

end LoanInsurance.Liquid
