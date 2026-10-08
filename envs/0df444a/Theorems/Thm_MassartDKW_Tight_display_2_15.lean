-- Prove2me | Theorems.Thm_MassartDKW_Tight_display_2_15
-- name    : MassartDKW.Tight.display_2_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:14:38.979727+00:00
-- url     : https://prove2.me/theorems/620f9347-b8f0-484e-a673-5b8f131c9077
-- title:
--   (2.15), p. 1283 — max_{n≤38} sup_{λ∈Λ_{η,n}} C_{λ,n} ≤ 0.951 on the grid λ = 1/2 + k/100 < √n
-- statement:
--   Let $\eta=10^{-2}$ and, for each $n$, $\Lambda_{\eta,n}=\{1/2+k\eta : k\in\mathbb N\}\cap[1/2,\sqrt n[$. Then, with $C_{\lambda,n}=\exp(2\lambda^2)\sum_{0\le j<n-\lambda\sqrt n}p_{\lambda,n}(j)$,
--   $$\max_{1\le n\le38}\ \sup_{\lambda\in\Lambda_{\eta,n}}C_{\lambda,n}\le0.951 .$$
--
--   The paper verifies this finite family of inequalities by computer, starting from the exact formula (2.3). With Proposition 2(iii) it closes the case $n\le38$ of Theorem 1.
--
--   **Formalization Note** The statement is the finite conjunction: for every $n$ with $1\le n\le38$ and every $k\in\mathbb N$ with $1/2+k/100<\sqrt n$, $C_{1/2+k/100,\,n}\le0.951$. A recomputation in 30-digit arithmetic gives the maximum $0.94955$, at $n=38$, $\lambda=1/2$.
-- source:
--   Massart, The tight constant in the Dvoretzky–Kiefer–Wolfowitz inequality, Ann. Probab. 18 (1990), p. 1283, (2.15)

import Mathlib
import Definitions.Def_MassartDKW_Tight_Analytic

namespace MassartDKW.Tight

theorem display_2_15 : ∀ n : ℕ, 1 ≤ n → n ≤ 38 → ∀ k : ℕ,
    (1 / 2 + (k : ℝ) * (1 / 100) : ℝ) < Real.sqrt n → C n (1 / 2 + (k : ℝ) * (1 / 100)) ≤ 0.951 := by sorry

end MassartDKW.Tight
