-- Prove2me | Theorems.Thm_LoanInsurance_Liquid_lemma_1
-- name    : LoanInsurance.Liquid.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:33:22.706535+00:00
-- url     : https://prove2.me/theorems/c4958539-a681-45a3-903b-77d04bf48933
-- title:
--   Lemma 1, p. 11 (PDF 15) — without loan insurance there is a unique interior liquid equilibrium, with threshold given by (6)
-- statement:
--   Consider the model without loan insurance. Assume the standing assumptions $A>0$, $0<\mu<\psi<1$, $0<\nu<1$, $\lambda>1$, $F$ a continuous distribution function on $[0,\bar\eta]$, strictly increasing there, and assume screening costs are heterogeneous enough:
--   $$\bar\eta>\frac{(1-\nu)(\psi-\mu)(1-\psi)}{\nu+(1-\nu)(1-\psi)}A.$$
--   Then:
--
--   1. the threshold equation
--   $$\eta^*=\frac{(1-\nu)(\psi-\mu)[1-\mu-(\psi-\mu)F(\eta^*)]}{\nu+(1-\nu)[1-\mu-(\psi-\mu)F(\eta^*)]}A\qquad(6)$$
--   has exactly one solution $\eta^*\in(0,\bar\eta)$;
--   2. for this solution the price $p^*_U=A-\eta^*/((1-\nu)(\psi-\mu))$ lies in $(0,A)$, so that $\underline\lambda_L=A/p^*_U\in(1,\infty)$;
--   3. if $\lambda\ge\underline\lambda_L$, i.e. $\lambda p^*_U\ge A$, then $(\eta^*,p^*_U)$ is a liquid equilibrium in the sense of Definition 3, and it is the only one.
--
--   This is the benchmark against which Proposition 2 compares the equilibrium with insurance.
--
--   **Formalization Note** "λ ≥ λ̲_L" is stated as $A\le\lambda p^*_U$, which is the same condition since $p^*_U>0$. Uniqueness is among all threshold profiles $(\eta,p_U)$ satisfying Definition 3 with (2).
-- source:
--   Ahnert & Kuncl, Loan Insurance, Market Liquidity, and Lending Standards, Bank of Canada Staff Working Paper 2019-47 (last updated August 2020), p. 11 (PDF 15), Lemma 1, (6); proof Appendix B.1, p. 39 (PDF 43)

import Mathlib
import Definitions.Def_LoanInsurance_Liquid_Model

namespace LoanInsurance.Liquid

/-- Lemma 1 (p. 11): without loan insurance, if screening costs are heterogeneous enough, the
threshold equation (6) has a unique interior solution `η*`, the price
`p*_U = A − η*/((1 − ν)(ψ − μ))` lies in `(0, A)`, and when `λ p*_U ≥ A` (that is, `λ ≥ λ̲_L`)
`(η*, p*_U)` is the unique liquid equilibrium of Definition 3. -/
theorem lemma_1 (P : Params) (hP : P.Standing)
    (hbar : (1 - P.ν) * (P.ψ - P.μ) * (1 - P.ψ) / (P.ν + (1 - P.ν) * (1 - P.ψ)) * P.A <
      P.etaBar) :
    (∃! η : ℝ, 0 < η ∧ η < P.etaBar ∧
        η = (1 - P.ν) * (P.ψ - P.μ) * (1 - P.μ - (P.ψ - P.μ) * P.F η) /
          (P.ν + (1 - P.ν) * (1 - P.μ - (P.ψ - P.μ) * P.F η)) * P.A) ∧
    ∀ η : ℝ, 0 < η → η < P.etaBar →
      η = (1 - P.ν) * (P.ψ - P.μ) * (1 - P.μ - (P.ψ - P.μ) * P.F η) /
          (P.ν + (1 - P.ν) * (1 - P.μ - (P.ψ - P.μ) * P.F η)) * P.A →
      0 < P.A - η / ((1 - P.ν) * (P.ψ - P.μ)) ∧ P.A - η / ((1 - P.ν) * (P.ψ - P.μ)) < P.A ∧
      (P.A ≤ P.lam * (P.A - η / ((1 - P.ν) * (P.ψ - P.μ))) →
        P.LiquidEqNoIns η (P.A - η / ((1 - P.ν) * (P.ψ - P.μ))) ∧
        ∀ η' p' : ℝ, P.LiquidEqNoIns η' p' →
          η' = η ∧ p' = P.A - η / ((1 - P.ν) * (P.ψ - P.μ))) := by sorry

end LoanInsurance.Liquid
