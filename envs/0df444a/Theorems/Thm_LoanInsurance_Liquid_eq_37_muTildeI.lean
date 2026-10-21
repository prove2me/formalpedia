-- Prove2me | Theorems.Thm_LoanInsurance_Liquid_eq_37_muTildeI
-- name    : LoanInsurance.Liquid.eq_37_muTildeI
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:33:24.540903+00:00
-- url     : https://prove2.me/theorems/45e55051-f390-4df6-b8fb-5493b6fc7e1d
-- title:
--   (37), p. 42 (PDF 46) — the bound µ̃_I defined by m* = 0 is unique, and insurance is used iff µ > µ̃_I
-- statement:
--   Fix $A,\psi,\nu,\lambda,\bar\eta,F$ satisfying the standing assumptions and view the repayment probability $\mu\in(0,\psi)$ as a parameter; write $m^*(\mu)$ for the share of Proposition 2 and $\underline\psi(\mu)=\lambda\mu/(\lambda\mu+\kappa(1-\mu))$. Assume screening costs are heterogeneous enough,
--   $$(1-\nu)\psi A\le\bar\eta,$$
--   so that $\eta^*(\mu)<\bar\eta$ for every $\mu\in(0,\psi)$. Then
--
--   1. there is exactly one $\tilde\mu_I\in(0,\psi)$ with $m^*(\tilde\mu_I)=0$, i.e. solving
--   $$\tilde\mu_I=\frac{\kappa\psi-(1-\psi)\lambda\frac{\tilde\mu_I}{1-\tilde\mu_I}}{(\lambda-1)(1-\nu)}\cdot\frac{F(\eta^*(\tilde\mu_I))}{1-F(\eta^*(\tilde\mu_I))};\qquad(37)$$
--   2. for every $\mu\in(0,\psi)$ with $\psi>\underline\psi(\mu)$, insurance is used (condition (35) holds) if and only if $\mu>\tilde\mu_I$.
--
--   Together with Proposition 2 this identifies the parameter region of a liquid equilibrium with insurance as $\{\mu>\tilde\mu_I,\ \lambda\ge\tilde\lambda_L\}$.
--
--   **Formalization Note** The paper writes $\tilde\mu_I\in(0,1)$; since $\mu<\psi<1$ the root lies in $(0,\psi)$. The heterogeneity assumption is added: the paper's existence argument ("follows from continuity in µ") needs $F(\eta^*(\mu))<1$ throughout. Without it the statement is false: if $\bar\eta$ is small, $F(\eta^*(\mu))=1$ wherever $\psi>\underline\psi(\mu)$, (35) never holds there, and no root exists. Since $\eta^*$ decreases in $\mu$ with supremum $(1-\nu)\psi A$ as $\mu\to0$, the assumption is exactly $\eta^*(0^+)\le\bar\eta$.
-- source:
--   Ahnert & Kuncl, Loan Insurance, Market Liquidity, and Lending Standards, Bank of Canada Staff Working Paper 2019-47 (last updated August 2020), p. 42 (PDF 46), (37) and the paragraph after it

import Mathlib
import Definitions.Def_LoanInsurance_Liquid_Model

namespace LoanInsurance.Liquid

/-- (37) (p. 42): fix `A, ψ, ν, λ, η̄, F` with screening costs heterogeneous enough that
`η*(μ) < η̄` for every `μ ∈ (0, ψ)` (namely `(1 − ν)ψA ≤ η̄`), and vary the repayment probability
`μ`. Then `m* = 0` has a unique root `μ̃_I ∈ (0, ψ)`, and for every `μ ∈ (0, ψ)` with `ψ > ψ̲(μ)`,
insurance is used ((35) holds) exactly when `μ > μ̃_I`. -/
theorem eq_37_muTildeI (P : Params) (hP : P.Standing)
    (hhet : (1 - P.ν) * P.ψ * P.A ≤ P.etaBar) :
    (∃! μt : ℝ, 0 < μt ∧ μt < P.ψ ∧ ({ P with μ := μt } : Params).mStar = 0) ∧
      ∀ μt : ℝ, 0 < μt → μt < P.ψ → ({ P with μ := μt } : Params).mStar = 0 →
        ∀ x : ℝ, 0 < x → x < P.ψ → ({ P with μ := x } : Params).psiUnder < P.ψ →
          (({ P with μ := x } : Params).Cond35 ↔ μt < x) := by sorry

end LoanInsurance.Liquid
