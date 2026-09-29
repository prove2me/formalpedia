-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_fieldBar_mul_intSeriesC_eq_and_reduction_eisensteinRatio
-- name    : ModularCurve.FullLevel.exists_fieldBar_mul_intSeriesC_eq_and_reduction_eisensteinRatio
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/a3f447a7-df71-5209-83b1-0ea8423fe5ad
-- title:
--   A unit of the full-level field reducing to E₄E₆/Δ
-- statement:
--   Let $q$ be a prime with $q \ge 5$ and let $M'$ be a nonzero natural number. Write $F = \mathrm{fieldBar}\,q\,M'$ for the intermediate field of $\overline{\mathbb{Q}}((T))$ over $\overline{\mathbb{Q}}$ obtained by base change to $\overline{\mathbb{Q}}$ of the function field `xHFunctionField` of level $q^2M'$ attached to the subgroup $H \le (\mathbb{Z}/q^2M')^\times$ which is the kernel of reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$. The assertion is that there are an element $u \in F$ and power series $X, Y \in \mathbb{Z}[[T]]$ with the following two properties. First, in $\overline{\mathbb{Q}}((T))$ one has $u \cdot Y = X$, where a power series over $\mathbb{Z}$ is sent to a Laurent series over a field $\kappa$ by coefficientwise base change, written `intSeriesC`. Second, for every field $\kappa$ of characteristic $q$, the image of $Y$ in $\kappa((T))$ is nonzero and $$\bar X \cdot \bar\Delta = \bar Y \cdot \bar E_4 \bar E_6 \quad\text{in } \kappa((T)),$$ where $\Delta$ is the integral series $T \cdot \mathrm{dedekindEtaUnit} = T\prod_{n \ge 1}(1 - T^n)^{24}$, and $E_4$, $E_6$ are the integral series with constant term $1$ and $n$-th coefficients $240\,\sigma_3(n)$ and $-504\,\sigma_5(n)$ for $n \ge 1$. Note that the characteristic-$q$ identity is stated in cross-multiplied form, and no nonvanishing of $\bar\Delta$ is claimed.
--
--   This produces, on one geometric component of the modular curve of level $\Gamma_H(q^2M')$ with $H$ the kernel of reduction modulo $q$, a function whose $q$-expansion is a ratio of integral series reducing modulo $q$ to the Eisenstein ratio $E_4E_6/\Delta$, the classical device of lifting the Hasse invariant (here via a pair of forms on $\Gamma_1(q)$ of weights $k+1$ and $k$ with congruent integral expansions). It feeds the construction of the family in [`ModularCurve.FullLevel.exists_family_liftIndep_gamma0`](thm.html#ModularCurve.FullLevel.exists_family_liftIndep_gamma0).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_fieldBar_mul_intSeriesC_eq_and_reduction_eisensteinRatio.lean

import Definitions.Def_ModularCurve_FullLevelJacobian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel CongruenceSubgroup
open scoped MatrixGroups ArithmeticFunction.sigma

theorem ModularCurve.FullLevel.exists_fieldBar_mul_intSeriesC_eq_and_reduction_eisensteinRatio
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] :
    ∃ (u : fieldBar q M') (X Y : PowerSeries ℤ),
      (u : LaurentSeries (AlgebraicClosure ℚ)) * intSeriesC (AlgebraicClosure ℚ) Y =
        intSeriesC (AlgebraicClosure ℚ) X ∧
      ∀ (κ : Type) [Field κ] [CharP κ q],
        intSeriesC κ Y ≠ 0 ∧
        intSeriesC κ X * intSeriesC κ (PowerSeries.X * dedekindEtaUnit) =
          intSeriesC κ Y *
            (intSeriesC κ (PowerSeries.mk fun n => if n = 0 then 1 else 240 * (σ 3 n : ℤ)) *
              intSeriesC κ (PowerSeries.mk fun n => if n = 0 then 1 else -504 * (σ 5 n : ℤ))) := by sorry
