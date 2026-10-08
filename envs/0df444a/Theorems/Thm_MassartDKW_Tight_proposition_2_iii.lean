-- Prove2me | Theorems.Thm_MassartDKW_Tight_proposition_2_iii
-- name    : MassartDKW.Tight.proposition_2_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:14:26.295438+00:00
-- url     : https://prove2.me/theorems/9911e7c2-ba39-435f-a204-7689618f7a65
-- title:
--   Proposition 2(iii), p. 1281 — slope of λ ↦ C_{λ,n} at most 3.61 for λ ≥ 1/2
-- statement:
--   Let $n\ge2$ and $C_{\lambda,n}=\exp(2\lambda^2)P(D_n^->\lambda)$. For $1/2\le\lambda_1\le\lambda_2<\sqrt n$,
--   $$C_{\lambda_2,n}-C_{\lambda_1,n}\le3.61\,(\lambda_2-\lambda_1).$$
--
--   With the grid check (2.15) at mesh $\eta=10^{-2}$ it gives $C_{\lambda,n}\le0.951+3.61\eta<1$ for all $n\le38$ and $1/2\le\lambda<\sqrt n$, which finishes the proof of Theorem 1.
--
--   **Formalization Note** The page states $\frac{d}{d\lambda}C_{\lambda,n}\le3.61$ for $\lambda\ge1/2$. Since $C_{\lambda,n}$ is continuous and piecewise smooth in $\lambda$ but has kinks, where Mathlib's derivative is the junk value $0$, the statement is the increment form, which is what the last step (p. 1283, "$0.951+\eta\cdot3.61$") uses and which follows from the derivative bound. $C_{\lambda,n}$ is `C n l`, defined through (2.3).
-- source:
--   Massart, The tight constant in the Dvoretzky–Kiefer–Wolfowitz inequality, Ann. Probab. 18 (1990), p. 1281, Proposition 2(iii)

import Mathlib
import Definitions.Def_MassartDKW_Tight_Analytic

namespace MassartDKW.Tight

theorem proposition_2_iii (n : ℕ) (hn : 2 ≤ n) :
    ∀ l₁ l₂ : ℝ, 1 / 2 ≤ l₁ → l₁ ≤ l₂ → l₂ < Real.sqrt n → C n l₂ - C n l₁ ≤ 3.61 * (l₂ - l₁) := by sorry

end MassartDKW.Tight
