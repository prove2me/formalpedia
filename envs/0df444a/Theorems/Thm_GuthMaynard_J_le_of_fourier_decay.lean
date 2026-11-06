-- Prove2me | Theorems.Thm_GuthMaynard_J_le_of_fourier_decay
-- name    : GuthMaynard.J_le_of_fourier_decay
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-05T19:14:24.540912+00:00
-- url     : https://prove2.me/theorems/4311c8af-a00f-447b-b71f-a32fdf837a1b
-- title:
--   Proposition 9.1 (Equidistribution over affine transformations)
-- statement:
--   Fix $K > 0$, $C \ge 1$ and a function $c(j, \varepsilon)$ of $j \in \mathbb N$ and $\varepsilon > 0$. For every $\delta > 0$ there is a constant $c'$ with the following property. Let $T > 0$, $M > 0$, and let $f : \mathbb R \to \mathbb R$ be smooth and nonnegative, supported in $[1/C, C]$, with
--   $$|\widehat f(\xi)| \le c(j, \varepsilon)\,T^{\varepsilon}\Big(\frac{T}{|\xi|}\Big)^j\sup_u f(u) \qquad (j \in \mathbb N,\ \varepsilon > 0,\ \xi \ne 0).$$
--   Then
--   $$J(f) \le c'\,T^{\delta}\Big(M^6\Big(\int f\Big)^2 + M^4\int f^2\Big).$$
--   Here $J(f)$ (`J M K f`, valued in $[0, \infty]$) is the supremum over $0 < M_1, M_2, M_3 < M$ of
--   $$\int\Big(\sum_{|m_1| \sim M_1,\ m_2 \sim M_2,\ |m_3| \le KM_3} f\Big(\frac{m_1u + m_3}{m_2}\Big)\Big)^2du,$$
--   with $A \sim B$ meaning $B < A \le 2B$, and $\widehat f(\xi) = \int f(u)e(-\xi u)\,du$.
--
--   **Formalization note.**
--   - The quantifiers follow the paragraph after the proposition (p. 29), which spells them out: $c'$ depends only on $C$ and the constants $c(j, \epsilon)$, and on $K$.
--   - $J(f)$'s range "$|m_3| \ll M_3$" has an implied constant, here $K$, and the statement holds for each fixed $K$.
--   - §9 defines $J(f)$ for a compactly supported smooth $f$, so smoothness is assumed.
--   - The decay bound is required only for $\xi \ne 0$: at $\xi = 0$ the factor $(T/|\xi|)^j$ is infinite.
-- source:
--   Guth, L. and Maynard, J., New large value estimates for Dirichlet polynomials, Ann. of Math. (2) 203 (2026) 623–675, https://doi.org/10.4007/annals.2026.203.2.6 (arXiv:2405.20552v2, whose page numbers are used), p. 29, Proposition 9.1 (Equidistribution over affine transformations)

import Mathlib
import Definitions.Def_GuthMaynard

namespace GuthMaynard

theorem J_le_of_fourier_decay (K C : ℝ) (hK : 0 < K) (hC : 1 ≤ C) (c : ℕ → ℝ → ℝ) :
    ∀ δ : ℝ, 0 < δ → ∃ c' : ℝ, ∀ T : ℝ, 0 < T → ∀ M : ℝ, 0 < M → ∀ f : ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) f → (∀ u, 0 ≤ f u) → Function.support f ⊆ Set.Icc (1 / C) C →
      (∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
        ‖FourierTransform.fourier (fun u => (f u : ℂ)) ξ‖ ≤
          c j ε * T ^ ε * (T / |ξ|) ^ j * ⨆ u, f u) →
      J M K f ≤ ENNReal.ofReal (c' * T ^ δ * (M ^ 6 * (∫ u, f u) ^ 2 + M ^ 4 * ∫ u, f u ^ 2)) := by
  sorry

end GuthMaynard
