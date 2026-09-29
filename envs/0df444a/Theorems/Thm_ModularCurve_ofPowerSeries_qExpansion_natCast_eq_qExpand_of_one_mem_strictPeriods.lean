-- Prove2me | Theorems.Thm_ModularCurve_ofPowerSeries_qExpansion_natCast_eq_qExpand_of_one_mem_strictPeriods
-- name    : ModularCurve.ofPowerSeries_qExpansion_natCast_eq_qExpand_of_one_mem_strictPeriods
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/9299af63-dfeb-5201-8580-9d4283a74a54
-- title:
--   Width-N q-expansion as q ↦ q^N substitution
-- statement:
--   Let $\Gamma$ be a subgroup of $\mathrm{GL}_2(\mathbb{R})$, let $k$ be an integer, and let $f$ be a modular form of weight $k$ on $\Gamma$, subject to the hypothesis that the real number $1$ lies in `Γ.strictPeriods`. Let $N$ be a nonzero natural number. For a positive real $h$, `UpperHalfPlane.qExpansion h` of the function underlying $f$ is the formal power series whose coefficients are the Taylor coefficients at $0$ of the associated cusp function in the variable $q = e^{2\pi i \tau / h}$. The assertion is an identity in the Laurent series $\mathbb{Z}$-indexed Hahn series over $\mathbb{C}$: the image under `HahnSeries.ofPowerSeries` of the width-$N$ expansion `UpperHalfPlane.qExpansion (N : ℝ) f` equals [`ModularCurve.qExpand ℂ N`](def/ModularCurve_X0.html#L25) applied to the image of the width-$1$ expansion `UpperHalfPlane.qExpansion 1 f`. Here [`ModularCurve.qExpand ℂ N`](def/ModularCurve_X0.html#L25) is the ring homomorphism on Laurent series obtained by embedding the index domain along multiplication by $N$ on $\mathbb{Z}$ (an injective, order-preserving map), that is, the substitution $q \mapsto q^N$: it sends a series with coefficients $a_n$ to the series whose coefficient at $Nn$ is $a_n$ and whose coefficients at exponents not divisible by $N$ vanish.
--
--   This is the classical comparison of $q$-expansions taken at different cusp widths: a form whose periods include $1$ has width-$N$ expansion $\hat f_1(q^N)$. It is used in the level-one/full-level comparisons of modular unit series, where expansions computed at width $N$ must be matched with level-one expansions at width $1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ofPowerSeries_qExpansion_natCast_eq_qExpand_of_one_mem_strictPeriods.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularCurve.ofPowerSeries_qExpansion_natCast_eq_qExpand_of_one_mem_strictPeriods
    {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (f : ModularForm Γ k) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods)
    (N : ℕ) [NeZero N] :
    HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion (N : ℝ) (⇑f : UpperHalfPlane → ℂ)) =
      ModularCurve.qExpand ℂ N
        (HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑f : UpperHalfPlane → ℂ))) := by sorry
