-- Prove2me | Theorems.Thm_FourExp_cauchy_estimate_with_zeros
-- name    : FourExp.cauchy_estimate_with_zeros
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-15T04:08:38.741763+00:00
-- url     : https://prove2.me/theorems/840a447e-cb2b-4bc8-9bc7-4496079c88d7
-- title:
--   A Cauchy estimate that uses the zeros of an entire function
-- statement:
--   **Cauchy's estimate, sharpened by zeros.**
--
--   Let $F$ be entire, $c \in \mathbb{C}$, $\rho \ge 0$ and $R > \rho + 1$. Let $S$ be a finite set of points with $|z - c| \le \rho$, and let $\sigma = \sum_{z \in S} \operatorname{ord}_z F$. If $|F| \le M$ on the circle $|z - c| = R$, then for every $s \ge 0$
--   $$|F^{(s)}(c)| \;\le\; s!\;\frac{R}{R-1}\Bigl(\frac{\rho+1}{R-\rho}\Bigr)^{\sigma} M .$$
--
--   **Proof idea.** Divide out the zeros: $G(z) = F(z) / \prod_{\beta \in S}(z - \beta)^{\operatorname{ord}_\beta F}$ is entire.
--   - On $|z - c| = R$ each factor has $|z - \beta| \ge R - \rho$, so $|G| \le M/(R-\rho)^\sigma$ there, and by the maximum principle everywhere inside.
--   - On $|z - c| = 1$ each factor has $|z - \beta| \le \rho + 1$, so $|F| \le M\bigl((\rho+1)/(R-\rho)\bigr)^\sigma$ there.
--   - Cauchy's estimate on the unit circle (`Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`) then gives the bound even without the factor $R/(R-1) \ge 1$.
--
--   The paper's argument is a double contour integral, which produces that factor.
--
--   **What it is for.** It is one of the two estimates behind `FourExp.expPoly_zero_count_scaled`.
-- source:
--   M. Waldschmidt, Indépendance algébrique des valeurs de la fonction exponentielle, Bull. Soc. Math. France 99 (1971), 285–304, §4, inequality (4.3).

import Mathlib

open Finset

namespace FourExp

theorem cauchy_estimate_with_zeros
    (F : ℂ → ℂ) (hF : Differentiable ℂ F) (c : ℂ) (ρ R M : ℝ) (hρ : 0 ≤ ρ) (hR : ρ + 1 < R)
    (S : Finset ℂ) (hS : ∀ z ∈ S, ‖z - c‖ ≤ ρ)
    (hM : ∀ z : ℂ, ‖z - c‖ = R → ‖F z‖ ≤ M) (s : ℕ) :
    ‖iteratedDeriv s F c‖
      ≤ (s.factorial : ℝ) * (R / (R - 1)) * ((ρ + 1) / (R - ρ)) ^ (∑ z ∈ S, analyticOrderNatAt F z) * M := by
  sorry

end FourExp
