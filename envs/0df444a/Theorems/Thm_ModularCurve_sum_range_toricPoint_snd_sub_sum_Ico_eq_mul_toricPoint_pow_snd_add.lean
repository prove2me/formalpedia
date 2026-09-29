-- Prove2me | Theorems.Thm_ModularCurve_sum_range_toricPoint_snd_sub_sum_Ico_eq_mul_toricPoint_pow_snd_add
-- name    : ModularCurve.sum_range_toricPoint_snd_sub_sum_Ico_eq_mul_toricPoint_pow_snd_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/2e7f0cff-4418-5835-bac3-af8c59f8e7ec
-- title:
--   Distribution relation for Tate's Y-series under μ_ℓ
-- statement:
--   Let $K$ be a field of characteristic $0$, let $\ell$ be a prime with $\ell \neq 2$, let $\zeta \in K$ be a primitive $\ell$-th root of unity, and let $c \in K$ satisfy $c \neq 0$ and $c^{\ell} \neq 1$. For $p \in \mathbb{N}$ and $u \in K$, `toricPoint K p u` is the pair of Laurent series over $K$ obtained from the power series whose first component has $m = 0$ coefficient $u/(1-u)^2$ and, for $m \geq 1$, coefficient $\sum_{d \mid m,\ p \mid d} (m/d)\,(u^{m/d} + u^{-m/d}) - 2[p \mid m]\,\sigma_1(m/p)$, and whose second component has $m = 0$ coefficient $u^2/(1-u)^3$ and, for $m \geq 1$, coefficient $\sum_{d \mid m,\ p \mid d} \bigl(\binom{m/d}{2} u^{m/d} - \binom{m/d+1}{2} u^{-m/d}\bigr) + [p \mid m]\,\sigma_1(m/p)$. The assertion is the identity of Laurent series $$\sum_{j=0}^{\ell-1} \bigl(\mathrm{toricPoint}\,K\,1\,(c\zeta^j)\bigr)_2 - \sum_{j=1}^{\ell-1} \bigl(\mathrm{toricPoint}\,K\,1\,(\zeta^j)\bigr)_2 = \ell^3 \cdot \bigl(\mathrm{toricPoint}\,K\,\ell\,(c^{\ell})\bigr)_2 + \tfrac{\ell^2(\ell-1)}{2}\cdot \bigl(\mathrm{toricPoint}\,K\,\ell\,(c^{\ell})\bigr)_1 - \tfrac{\ell^2-1}{24},$$ where $\ell^3$ is the cube of the image of $\ell$ in the Laurent series ring and the two scalars $\ell^2(\ell-1)/2$ and $(\ell^2-1)/24$ of $K$ enter as constant Laurent series via `HahnSeries.C`.
--
--   This is the distribution (norm) relation satisfied by the second coordinate of Tate's parametrisation: summing Tate's $Y(u,q)$ over the $\mu_\ell$-orbit of $u = c$, normalised by the orbit sum at $u = 1$, produces $Y(c^\ell, q^\ell)$ together with a cross term in $X(c^\ell,q^\ell)$ and a constant. It is used in the verification that Vélu's formulae for the quotient of the Tate curve by $\mu_\ell$ carry toric points to toric points on the Tate curve with parameter $q^\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_sum_range_toricPoint_snd_sub_sum_Ico_eq_mul_toricPoint_pow_snd_add.lean

import Mathlib
import Definitions.Def_ModularCurve_TateSlots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

universe u

theorem ModularCurve.sum_range_toricPoint_snd_sub_sum_Ico_eq_mul_toricPoint_pow_snd_add
    (K : Type u) [Field K] [CharZero K] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2)
    (ζ : K) (hζ : IsPrimitiveRoot ζ ℓ) (c : K) (hc0 : c ≠ 0) (hcℓ : c ^ ℓ ≠ 1) :
    ∑ j ∈ Finset.range ℓ, (toricPoint K 1 (c * ζ ^ j)).2 -
        ∑ j ∈ Finset.Ico 1 ℓ, (toricPoint K 1 (ζ ^ j)).2 =
      (ℓ : LaurentSeries K) ^ 3 * (toricPoint K ℓ (c ^ ℓ)).2 +
        HahnSeries.C ((ℓ : K) ^ 2 * ((ℓ : K) - 1) / 2) * (toricPoint K ℓ (c ^ ℓ)).1 -
          HahnSeries.C (((ℓ : K) ^ 2 - 1) / 24) := by sorry
