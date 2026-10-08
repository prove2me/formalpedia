-- Prove2me | Theorems.Thm_LLLFactor_Factors_card_le_2_18
-- name    : LLLFactor.Factors.card_le_2_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:24:06.266004+00:00
-- url     : https://prove2.me/theorems/6302bb22-33bb-491b-bf37-87b34fce1534
-- title:
--   (2.18), proof of (2.16), p. 529 — linearly independent b_j of degree ≤ m all divisible by h₁: #J ≤ m + 1 − deg h₁
-- statement:
--   Let $m\ge0$ and let $b_1,\dots,b_{m+1}\in\mathbb Z[X]$ have degree at most $m$ and linearly independent coefficient vectors in $\mathbb R^{m+1}$. Let $J\subseteq\{1,\dots,m+1\}$ and let $h_1\in\mathbb Z[X]$ be a nonzero polynomial dividing $b_j$ for every $j\in J$. Then
--   $$\text{(2.18)}\qquad \#J\le m+1-\deg h_1.$$
--
--   Each $b_j$ with $j\in J$ lies in $\mathbb Z h_1+\mathbb Zh_1X+\dots+\mathbb Zh_1X^{m-\deg h_1}$, a space of rank $m+1-\deg h_1$; this counting bound is half of the squeeze that determines $t$ in Proposition (2.16).
--
--   **Formalization Note** On the page $h_1=\gcd(\{b_j:j\in J\})$; the statement is given for any nonzero common divisor $h_1$, which contains the page's case. The right-hand side is a natural-number difference; when $\deg h_1>m$ it is $0$ and the statement says $J=\varnothing$, which is correct because no nonzero polynomial of degree $\le m$ is divisible by $h_1$. Indices are 0-based.
-- source:
--   Lenstra, Lenstra, Lovász, Factoring polynomials with rational coefficients, Math. Ann. 261 (1982), p. 529, (2.18) in the proof of (2.16) Proposition

import Mathlib
import Definitions.Def_LLLFactor_Factors_Setting

open Polynomial

namespace LLLFactor.Factors

theorem card_le_2_18 (m : ℕ) (b : Fin (m + 1) → ℤ[X])
    (hli : LinearIndependent ℝ (coeffVec m ∘ b)) (hdeg : ∀ j, (b j).natDegree ≤ m)
    (J : Finset (Fin (m + 1))) (h₁ : ℤ[X]) (hh₁ : h₁ ≠ 0) (hdvd : ∀ j ∈ J, h₁ ∣ b j) :
    J.card ≤ m + 1 - h₁.natDegree := by sorry

end LLLFactor.Factors
