-- Prove2me | Theorems.Thm_LefebvreVariations_li_coefficients_pos_lt_ten
-- name    : LefebvreVariations.li_coefficients_pos_lt_ten
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:30:17.675461+00:00
-- url     : https://prove2.me/theorems/41185b16-effd-5c24-bb48-b908c50d96d2
-- title:
--   Lefebvre's variations, No. 171 — on a theme by Li: the first ten Li coefficients are positive
-- statement:
--   Let $\xi(s)=\tfrac12\bigl(1+s(s-1)\Lambda_0(s)\bigr)$ be the Riemann xi function and let
--   $$
--   \lambda_n=\frac1{(n-1)!}\,\frac{d^n}{ds^n}\Bigl[s^{n-1}\log\xi(s)\Bigr]_{s=1}
--   $$
--   be the Li coefficients. Then $\lambda_n>0$ for $n=1,2,\dots,10$. Numerically, $\lambda_1\approx0.0231$, $\lambda_2\approx0.0923$, $\lambda_3\approx0.2076$, $\lambda_4\approx0.3688$, $\lambda_5\approx0.5755$, and $\lambda_{10}\approx2.2793$.
--
--   Li's criterion states that the Riemann hypothesis is equivalent to $\lambda_n\ge0$ for all $n\ge1$. The coefficients can be computed exactly from derivatives of $\log\xi$ at $s=1$ and are known numerically far beyond $n=10$; this is the first block of the infinite family.
--
--   **Formalization Note** In Lean, `xi s := (1 + s * (s - 1) * completedRiemannZeta₀ s) / 2`, and for `n : ℕ` the real part of `iteratedDeriv (n+1) (fun s => s ^ n * Complex.log (xi s)) 1 / n!` is $\lambda_{n+1}$, exactly as in `BroughanRH.liCoefficient`. The statement quantifies over `n < 10` (so $\lambda_1,\dots,\lambda_{10}$) with a strict inequality. The principal logarithm is analytic near $s=1$ because $\xi(1)=1/2$.
--
--   **Why this is a variation.** This varies the open platform problem `BroughanRH.liPositive` (and `BroughanRH.liCoefficient`), Li's criterion: positivity of all Li coefficients, equivalent to the Riemann hypothesis. It is the first finite block $\lambda_1,\dots,\lambda_{10}$ of the infinite family, stated with the parent's own `xi` and index convention. The coefficients are explicit derivatives of $\log\xi$ at $s=1$, so the statement is a finite computation that the general problem must contain.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Xian-Jin Li, The positivity of a sequence of numbers and the Riemann hypothesis, J. Number Theory 65 (1997) 325-333 (Li's criterion). Numerical values of the Li coefficients: Keiper, Math. Comp. 58 (1992) 765-773; Maslanka (Acta Cosmologica 2004); Voros (asymptotics of lambda_n). (All cited from memory; page numbers not verified.) The values lambda_1 .. lambda_10 = 0.0230957, 0.0923457, 0.207639, 0.368790, 0.575543, 0.827566, 1.12446, 1.46576, 1.85092, 2.27934 were recomputed numerically (mpmath, 80 digits, derivatives of s^n log xi at s = 1) and are all positive. Origin of this statement: the first ten cases of Li's criterion, formalized as the platform theorems BroughanRH.liCoefficient (non-strict) and BroughanRH.liPositive (strict).

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

/-- **The first ten Li coefficients are positive.** With `ξ(s) = (1 + s(s-1)Λ₀(s))/2` the Riemann xi function,
the Li coefficients `λ_{n+1} = (1/n!) (d/ds)^{n+1} [ s^n log ξ(s) ]_{s=1}` are strictly positive for
`n = 0, …, 9`; numerically `λ₁ ≈ 0.0231, λ₂ ≈ 0.0923, λ₃ ≈ 0.2076, λ₄ ≈ 0.3688, …, λ₁₀ ≈ 2.2793`.
Li's criterion (X.-J. Li, J. Number Theory 65 (1997) 325–333, cited from memory) says that the Riemann
hypothesis is equivalent to `λ_n ≥ 0` for all `n ≥ 1`; this is the finite range `n ≤ 10`, which has been
checked far beyond by Keiper, Maslanka and Voros (cited from memory).

**Formalization Note.** Same `xi` and same expression as `BroughanRH.liCoefficient` and
`BroughanRH.liPositive` (index shifted by one as there), quantified over `n < 10` with a strict
inequality. The logarithm is the principal one, analytic near `s = 1` because `ξ(1) = 1/2`. -/
theorem li_coefficients_pos_lt_ten :
    let xi (s : ℂ) : ℂ := (1 + s * (s - 1) * completedRiemannZeta₀ s) / 2
    ∀ n : ℕ, n < 10 →
      0 < ((iteratedDeriv (n + 1) (fun s : ℂ => s ^ n * Complex.log (xi s)) 1) /
        (n.factorial : ℂ)).re := by
  sorry

end LefebvreVariations
