-- Prove2me | Theorems.Thm_GroupBuyEq_Signup_integral_equation_iff
-- name    : GroupBuyEq.Signup.integral_equation_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:20:44.055926+00:00
-- url     : https://prove2.me/theorems/79f202e4-c2bc-4fde-a2fc-d638de7779fa
-- title:
--   Proof of Proposition 1, (A.6)–(A.14), pp. A.2–A.3 — the conditioning equation (4) is equivalent to the closed form (A.14)
-- statement:
--   Let $\lambda>0$ and $T>0$, and let $h,g,\pi:\mathbb R\to\mathbb R$ be measurable, with $h(t),g(t)\in[0,1]$ for $t\in[0,T]$ and $\pi$ bounded on $[0,T]$. Then $\pi$ solves the conditioning equation
--   $$\pi(t)=\int_0^{T-t}\big(h(t+x)g(t+x)+(1-h(t+x))\pi(t+x)\big)\lambda e^{-\lambda x}\,dx\qquad\text{for all }t\in[0,T]$$
--   if and only if
--   $$\pi(t)=\lambda\int_t^T e^{-\lambda\int_t^s h(v)\,dv}\,h(s)\,g(s)\,ds\qquad\text{for all }t\in[0,T].$$
--
--   With $h=H_k$, $g=\pi^2_{k+1}$ and $\pi=\pi^2_k$ the first equation is (4) and the second is (A.14), the recursion (6) of Proposition 1; with $\pi^1$ in place of $\pi^2$ it is (5). The forward direction is the derivation in the proof of Proposition 1, and it gives uniqueness of each $\pi^i_k$ given $\pi^i_{k+1}$; the backward direction shows that the recursion produces a solution, which gives existence.
--
--   **Formalization Note** The page quotes (A.14) as $\pi^2_k(t)=\lambda_g\int_t^T e^{-\lambda_g\int_t^u H_k(v)dv}\lambda_g H_k(u)\pi^2_{k+1}(u)du$ with a doubled factor $\lambda_g$; (A.13) and (6) have a single factor, which is the form stated. The integration variable $u$ of (A.14) is renamed $s$. The paper differentiates (4) without stating regularity; the statement assumes only measurability and the bounds above, which make every integral genuine.
-- source:
--   Ming & Tunca, Consumer Equilibrium, Demand Effects, and Efficiency in Group Buying, SSRN 3352047 (version of 2020-05-15), pp. A.2–A.3 (PDF 35–36), proof of Proposition 1, (A.6)–(A.14)

import Mathlib
import Definitions.Def_GroupBuyEq_Signup_Model

namespace GroupBuyEq.Signup

theorem integral_equation_iff (lam T : ℝ) (hlam : 0 < lam) (hT : 0 < T) (h g π : ℝ → ℝ)
    (hh : Measurable h) (hg : Measurable g) (hπ : Measurable π)
    (hh01 : ∀ t ∈ Set.Icc 0 T, h t ∈ Set.Icc (0 : ℝ) 1)
    (hg01 : ∀ t ∈ Set.Icc 0 T, g t ∈ Set.Icc (0 : ℝ) 1)
    (hπb : ∃ C : ℝ, ∀ t ∈ Set.Icc 0 T, |π t| ≤ C) :
    (∀ t ∈ Set.Icc 0 T, π t = ∫ x in (0 : ℝ)..(T - t),
        (h (t + x) * g (t + x) + (1 - h (t + x)) * π (t + x)) * lam * Real.exp (-(lam * x))) ↔
      (∀ t ∈ Set.Icc 0 T,
        π t = lam * ∫ s in t..T, Real.exp (-(lam * ∫ v in t..s, h v)) * h s * g s) := by sorry

end GroupBuyEq.Signup
