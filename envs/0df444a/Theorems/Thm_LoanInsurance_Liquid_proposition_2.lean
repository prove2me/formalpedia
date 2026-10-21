-- Prove2me | Theorems.Thm_LoanInsurance_Liquid_proposition_2
-- name    : LoanInsurance.Liquid.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:33:27.208498+00:00
-- url     : https://prove2.me/theorems/4d82fc0e-127a-49b9-93a7-b979ba89f106
-- title:
--   Proposition 2 (existence, parts 1–2), p. 15 (PDF 19) — a liquid equilibrium with loan insurance exists with explicit η*, p*_U, m*; insurance raises p_U and lowers screening
-- statement:
--   Assume the standing assumptions of the model, $A>0$, $0<\mu<\psi<1$, $0<\nu<1$, $\lambda>1$, and screening costs with a continuous distribution function $F$ strictly increasing on its support $[0,\bar\eta]$. Assume further
--
--   1. productive screening, $\psi>\underline\psi=\dfrac{\lambda\mu}{\lambda\mu+\kappa(1-\mu)}$ with $\kappa=\nu\lambda+1-\nu$;
--   2. a large enough liquidity shock, $\lambda\ge\tilde\lambda_L=\dfrac1{2\mu}+\sqrt{\dfrac1{4\mu^2}+\dfrac{(1-\mu)(1-\nu)}{\mu\nu}}$;
--   3. condition (35), equivalent to $\mu>\tilde\mu_I$.
--
--   Then there exists a liquid equilibrium with loan insurance (Definition 1) in which screeners do not insure and a share $m^*\in(0,1)$ of high-cost lenders insures, with
--   $$\eta^*=\frac{(1-\nu)(1-\mu)(\psi-\mu)\kappa A}{\nu\lambda+(1-\nu)(1-\mu)},\qquad p^*_U=\frac{\nu\lambda\mu A}{\nu\lambda+(1-\nu)(1-\mu)},$$
--   $$m^*=1-\frac{(\kappa(1-\mu)\psi-(1-\psi)\lambda\mu)F(\eta^*)}{\mu(\lambda-1)(1-\nu)(1-\mu)(1-F(\eta^*))},$$
--   insurance fee $k^*=(1-\mu)A$ and insured price $p^*_I=\mu A$. Moreover $p^*_U\in[A/\lambda,\,p^*_I)$. Finally (part 1), loan insurance raises the price of uninsured loans and lowers screening: for every solution $(\eta_0,p_0)$ of the no-insurance system, price (4) and threshold (5),
--   $$p_0<p^*_U\qquad\text{and}\qquad\eta^*<\eta_0.$$
--
--   This is the paper's main positive result: insurance at origination improves the pool of uninsured loans traded and so their price, at the cost of weaker lending standards.
--
--   **Formalization Note** The paper's hypothesis $\mu>\tilde\mu_I$ is replaced by condition (35), by which Appendix B.3 defines $\tilde\mu_I$ (their equivalence is milestone (37)). The assumption $\psi>\underline\psi$ is the paper's standing focus (p. 14, "which we focus on henceforth"; footnote 18). Part 1 compares with every solution of (4)–(5), which includes the equilibrium of Lemma 1 whenever it exists. The comparative statics of part 3 are not formalized.
-- source:
--   Ahnert & Kuncl, Loan Insurance, Market Liquidity, and Lending Standards, Bank of Canada Staff Working Paper 2019-47 (last updated August 2020), p. 15 (PDF 19), Proposition 2 (existence, parts 1–2); proof Appendix B.3, pp. 41–43 (PDF 45–47)

import Mathlib
import Definitions.Def_LoanInsurance_Liquid_Model

namespace LoanInsurance.Liquid

/-- Proposition 2 (p. 15), existence and parts 1–2: for `ψ > ψ̲`, `λ ≥ λ̃_L` and (35)
(`μ > μ̃_I`), there is a liquid equilibrium (Definition 1) in which high-cost lenders insure with
share `m* ∈ (0, 1)`, with threshold `η*`, price `p*_U ∈ [A/λ, p*_I)`, fee `(1 − μ)A` and
`p*_I = μA`; and compared with every solution of the no-insurance system (4)–(5), the price of
uninsured loans is higher and the screening threshold lower. -/
theorem proposition_2 (P : Params) (hP : P.Standing) (hψ : P.psiUnder < P.ψ)
    (hlam : P.lamTildeL ≤ P.lam) (h35 : P.Cond35) :
    (∃ e : Profile, P.LiquidEq e ∧ 0 < e.m ∧ e.m < 1 ∧ e.mL = 0 ∧
        e.eta = P.etaStar ∧ e.pU = P.pUStar ∧ e.m = P.mStar ∧
        e.k = (1 - P.μ) * P.A ∧ e.pI = P.μ * P.A) ∧
      P.A / P.lam ≤ P.pUStar ∧ P.pUStar < P.μ * P.A ∧
      ∀ η₀ p₀ : ℝ, P.BenchmarkFP η₀ p₀ → p₀ < P.pUStar ∧ P.etaStar < η₀ := by sorry

end LoanInsurance.Liquid
