-- Prove2me | Theorems.Thm_LiuVanRyzin_focLHS_unique_root
-- name    : LiuVanRyzin.focLHS_unique_root
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T15:37:56.83399+00:00
-- url     : https://prove2.me/theorems/2f297eb1-e631-415e-8a01-a4c123536dcb
-- title:
--   §3.1, root of Eq. (7) — the first-order condition has a unique root $v^0>p_1$
-- statement:
--   Let $p_2<p_1$, $\alpha<p_2$ and $0<\gamma<1$, and write
--   $$\Phi(v)=\left(\frac{v-p_1}{v-p_2}\right)^\gamma\left(1+\frac{\gamma(p_1-p_2)}{v-p_1}\right)-\frac{p_1-\alpha}{p_2-\alpha}$$
--   for the left-hand side of the first-order condition (7). Then
--
--   1. $\Phi$ is strictly decreasing on $v>p_1$;
--   2. $\Phi(v)>0$ for all $v>p_1$ close enough to $p_1$;
--   3. $\Phi(v)<0$ for all sufficiently large $v$;
--   4. there is exactly one $v^0>p_1$ with $\Phi(v^0)=0$.
--
--   The root $v^0$ is the interior candidate for the optimal cutoff in Lemma 1 and Proposition 3. Since $\Phi$ does not involve $\bar U$, neither does $v^0$.
--
--   **Formalization Note** "Opposite signs at $v\to p_1^+$ and $v\to+\infty$" is stated as eventual positivity along the right neighbourhood filter of $p_1$ and eventual negativity along `atTop`.
-- source:
--   Liu, van Ryzin, Strategic Capacity Rationing to Induce Early Purchases, Management Science 54(6):1115–1131 (2008), p. 1122, §3.1, root of Eq. (7) (text following Lemma 1)

import Mathlib
import Definitions.Def_LiuVanRyzin_PowerModel

namespace LiuVanRyzin

open Filter Topology

/-- §3.1, root of Eq. (7) (Liu–van Ryzin 2008, p. 1122). The left-hand side of (7) strictly
decreases in `v > p₁`, is positive as `v → p₁⁺` and negative as `v → +∞`; hence (7) has a unique
root `v⁰ > p₁`. -/
theorem focLHS_unique_root (p₁ p₂ α γ : ℝ) (hα : α < p₂) (hp : p₂ < p₁)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    StrictAntiOn (focLHS p₁ p₂ α γ) (Set.Ioi p₁) ∧
      (∀ᶠ v in 𝓝[>] p₁, 0 < focLHS p₁ p₂ α γ v) ∧
      (∀ᶠ v in atTop, focLHS p₁ p₂ α γ v < 0) ∧
      ∃! v₀ : ℝ, p₁ < v₀ ∧ focLHS p₁ p₂ α γ v₀ = 0 := by sorry

end LiuVanRyzin
