-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_modularForm_qExpansion_eq_coeff_toricGenKernel_and_slash_conjElemN_eq
-- name    : ModularCurve.FullLevel.AuxLevel.exists_modularForm_qExpansion_eq_coeff_toricGenKernel_and_slash_conjElemN_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:22.181174+00:00
-- url     : https://prove2.me/theorems/ebdcaa44-3e0b-5fc3-911a-5fcd0c9efd43
-- title:
--   Toric generator-kernel coefficients as q-expansions of modular forms
-- statement:
--   Let $q$ be a prime with $q\ge 5$, let $M'$ be a nonzero natural number with $q\nmid M'$, and let $\ell$ be a prime with $\ell\ge 3$, $\ell\ne q$ and $\ell\nmid M'$; let $p$ be a prime, $k$ a natural number with $p^{k}\mid M'$, and $\zeta\in\mathbb{C}$ a primitive $p^{k}$-th root of unity. Write $N=q\ell$ and $D=$ [`ModularCurve.gamma0PowDeg p k`](def/ModularCurve_WeierstrassGamma0Pow.html#L53), which is $1$ if $p^{k}=2$ and $\varphi(p^{k})/2$ otherwise. The assertion is that for every $j\le D$ there is a modular form $S$ of weight $2(D-j)$ (the subtraction taken in $\mathbb{N}$) on the subgroup of $\mathrm{GL}_2(\mathbb{R})$ attached to [`CohCarrier.GammaH`](def/CohCarrier_Level.html#L133), that is, on the image of those $\gamma\in\Gamma_0(N^{2}M')$ whose lower right entry, read through `gamma0Units`, lies in [`ModularCurve.FullLevel.levelH N M'`](def/ModularCurve_FullLevelJacobian.html#L22), the kernel of the unit-group reduction `ZMod.unitsMap (dvd_sq_mul N M')` on $(\mathbb{Z}/N^{2}M')^{\times}$, such that two conditions hold. First, the Laurent-series image under `HahnSeries.ofPowerSeries` of the width-$1$ $q$-expansion of $S$ equals the coefficient of $X^{j}$ in the polynomial, with coefficients in Laurent series over $\mathbb{C}$, $$\prod_{1\le a\le p^{k}/2,\ p\nmid a}\bigl(X-(x_a+\tfrac{1}{12})\bigr),$$ where $x_a$ is the first coordinate of [`ModularCurve.toricPoint ℂ N (ζ ^ a)`](def/ModularCurve_TateSlots.html#L125), namely the power series with constant term $c/(1-c)^{2}$ and $m$-th coefficient $\sum_{e\mid m,\ N\mid e}(m/e)\,(c^{m/e}+c^{-m/e})-2\,[N\mid m]\sum_{f\mid m/N}f$ for $c=\zeta^{a}$, and $\tfrac1{12}$ is the constant Hahn series. Second, for every $\rho\in \mathrm{SL}_2(\mathbb{Z})$ with $\rho\in\Gamma_0(M')$, the function $S$ is fixed by the weight-$2(D-j)$ slash action of [`ModularCurve.FullLevel.conjElemN N ρ`](def/ModularCurve_FullLevelLevelAutAt.html#L13), the real matrix $\begin{pmatrix}a&b/N\\ Nc&d\end{pmatrix}=\mathrm{diag}(N,1)^{-1}\rho\,\mathrm{diag}(N,1)$.
--
--   Classically, $x(\zeta^{a})+\tfrac1{12}$ is $(2\pi i)^{-2}\wp(a/p^{k};Nz)$, a weight-two Eisenstein series of level $p^{k}$ evaluated at $Nz$, so the elementary symmetric functions of these quantities over the classes $a\in(\mathbb{Z}/p^{k})^{\times}/\{\pm1\}$ are modular forms of even weight, invariant under the elements of $\Gamma_0(M')$ conjugated by $\mathrm{diag}(N,1)$; the statement packages this as an existence result for the coefficients of the monic polynomial whose roots are those quantities. It is used in the analysis of the $p^{k}$-division structure on the Tate curve entering [`ModularCurve.FullLevel.level_fst_act_mapRing_eq_of_curve_eq_units_of_level_fst_gamma0Pow`](thm.html#ModularCurve.FullLevel.level_fst_act_mapRing_eq_of_curve_eq_units_of_level_fst_gamma0Pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_exists_modularForm_qExpansion_eq_coeff_toricGenKernel_and_slash_conjElemN_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularCurve.FullLevel.AuxLevel.exists_modularForm_qExpansion_eq_coeff_toricGenKernel_and_slash_conjElemN_eq
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')

    (p k : ℕ) [Fact p.Prime] (hpk : p ^ k ∣ M') (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (p ^ k)) :
    haveI : NeZero (q * ℓ) := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero⟩
    ∀ j : ℕ, j ≤ ModularCurve.gamma0PowDeg p k →
      ∃ S : ModularForm (CohCarrier.GammaH ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') :
            Subgroup (GL (Fin 2) ℝ)) (2 * ((ModularCurve.gamma0PowDeg p k - j : ℕ) : ℤ)),
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑S)) =
          (∏ a ∈ (Finset.Icc 1 (p ^ k / 2)).filter (fun a => ¬ p ∣ a),
            (Polynomial.X - Polynomial.C ((ModularCurve.toricPoint ℂ (q * ℓ) (ζ ^ a)).1 + HahnSeries.C ((12 : ℂ)⁻¹)))).coeff j ∧
        ∀ ρ : SL(2, ℤ), ρ ∈ CongruenceSubgroup.Gamma0 M' →
          (⇑S ∣[(2 * ((ModularCurve.gamma0PowDeg p k - j : ℕ) : ℤ))] ModularCurve.FullLevel.conjElemN (q * ℓ) ρ) = ⇑S := by sorry
