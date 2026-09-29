-- Prove2me | Theorems.Thm_MvPowerSeries_exists_eq_X_sub_subst_mul_of_subst_eq_zero
-- name    : MvPowerSeries.exists_eq_X_sub_subst_mul_of_subst_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/bc458f3f-f80a-52a7-81ee-226dbd34e439
-- title:
--   Factor theorem in R[[X₀,X₁]] for a root X₁=φ(X₀)
-- statement:
--   Let $R$ be a commutative ring, let $f$ be a formal power series in two variables over $R$, i.e. an element of `MvPowerSeries (Fin 2) R`, and let $\varphi$ be a univariate power series in `PowerSeries R` whose constant coefficient vanishes. Assume that $f$ vanishes when its two variables are substituted by $X$ and $\varphi$ respectively, that is, `MvPowerSeries.subst ![PowerSeries.X, φ] f = 0` in `PowerSeries R`; informally, $f(T,\varphi(T)) = 0$. The conclusion is that there exists $M \in$ `MvPowerSeries (Fin 2) R` with
--   $$f = \bigl(X_1 - \varphi(X_0)\bigr)\, M ,$$
--   where $X_0, X_1$ are the two variables of `MvPowerSeries (Fin 2) R` and $\varphi(X_0)$ denotes `PowerSeries.subst (X 0) φ`, the substitution of the two-variable series $X_0$ for the variable of $\varphi$ (legitimate because $\varphi$ has zero constant term). No hypothesis of Noetherianity, completeness or regularity on $R$ is required, and no condition beyond $\varphi(0)=0$ is imposed on $\varphi$.
--
--   This is the factor theorem for two-variable power series: a power series vanishing identically along the branch $X_1 = \varphi(X_0)$, with $\varphi(0)=0$, is divisible by $X_1 - \varphi(X_0)$. It is used in the form needed by [`MvPowerSeries.exists_eq_mul_of_sub_mul_prod_linear_mem_pow_of_det_ne_zero`](thm.html#MvPowerSeries.exists_eq_mul_of_sub_mul_prod_linear_mem_pow_of_det_ne_zero), where a two-variable series known to vanish on such a branch must be split off a linear factor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPowerSeries_exists_eq_X_sub_subst_mul_of_subst_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open MvPowerSeries

theorem MvPowerSeries.exists_eq_X_sub_subst_mul_of_subst_eq_zero
    {R : Type u} [CommRing R] (f : MvPowerSeries (Fin 2) R)
    (φ : PowerSeries R) (hφ0 : PowerSeries.constantCoeff φ = 0)
    (hroot : MvPowerSeries.subst ![(PowerSeries.X : PowerSeries R), φ] f = 0) :
    ∃ M : MvPowerSeries (Fin 2) R,
      f = (X 1 - PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) R) φ) * M := by sorry
