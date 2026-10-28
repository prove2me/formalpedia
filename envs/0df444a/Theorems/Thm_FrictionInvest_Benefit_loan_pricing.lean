-- Prove2me | Theorems.Thm_FrictionInvest_Benefit_loan_pricing
-- name    : FrictionInvest.Benefit.loan_pricing
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T02:33:56.711317+00:00
-- url     : https://prove2.me/theorems/dc8c387e-41ce-4b7d-8e7b-a28aa987fc57
-- title:
--   Equation (2), p. 92 — the loan face value solves the bank zero-profit equation
-- statement:
--   Let $p,a,c>0$, $y\ge0$, $\gamma\in[0,1]$, and let $q\ge0$ require a loan. Suppose the discriminant is positive and the resulting face value $F(q)$ satisfies the bank's loan limit. Then $F(q)>0$, $(1+\gamma)F(q)<ap$, and
--   $$\mathbb E[\min(p\min(q,\xi),F(q))]-\mathbb E[\gamma p\min(q,\xi)\mathbf1_{p\min(q,\xi)\le F(q)}]=cq-y.$$
--   It is the unique nonnegative solution within the stated lending region. This identifies the model's closed-form face value with the competitive bank-pricing equation.
--
--   **Formalization Note** The theorem concerns the positive-loan branch; the paper's Assumptions 2 and 3 restrict this branch.
-- source:
--   Tanrisever, Joglekar, Erzurumlu & Lévesque, Managing capital market frictions via cost-reduction investments, M&SOM 23(1), 2021, p. 92 (PDF 5), §3, equations (1)–(2) and Assumptions 2–3

import Mathlib
import Definitions.Def_FrictionInvest_Benefit_Model

namespace FrictionInvest.Benefit

/-- Competitive loan pricing, equations (1)–(2), on the borrowing branch. -/
theorem loan_pricing (P : Params) (hp : 0 < P.p) (ha : 0 < P.a)
    (γ c y q : ℝ) (hγ : 0 ≤ γ ∧ γ ≤ 1) (hc : 0 < c) (hy : 0 ≤ y)
    (hq : 0 ≤ q) (hborrow : y < c * q)
    (hbound : 2 * (1 + γ) * (c * q - y) < P.a * P.p)
    (hloan : faceValue P γ c y q < q * P.p) :
    0 < faceValue P γ c y q ∧
    (1 + γ) * faceValue P γ c y q < P.a * P.p ∧
    bankReceipt P γ q (faceValue P γ c y q) = c * q - y ∧
    ∀ F' : ℝ, 0 ≤ F' → (1 + γ) * F' < P.a * P.p → F' < q * P.p →
      bankReceipt P γ q F' = c * q - y → F' = faceValue P γ c y q := by sorry

end FrictionInvest.Benefit
