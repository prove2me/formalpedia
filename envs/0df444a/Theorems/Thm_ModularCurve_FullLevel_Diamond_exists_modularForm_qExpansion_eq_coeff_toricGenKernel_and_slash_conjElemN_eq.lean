-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_exists_modularForm_qExpansion_eq_coeff_toricGenKernel_and_slash_conjElemN_eq
-- name    : ModularCurve.FullLevel.Diamond.exists_modularForm_qExpansion_eq_coeff_toricGenKernel_and_slash_conjElemN_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/741e6ebe-14e4-5408-9507-5728d667d69a
-- title:
--   Toric generator-kernel coefficients as modular forms on Γ_{H_1}
-- statement:
--   Let $q$ be a prime, let $M'\ge 1$ with $q\nmid M'$, let $\ell_g$ be a prime with $\ell_g\equiv 11\pmod{12}$ and $\ell_g\mid M'$, and let $H_1\le(\mathbb Z/q^2M')^\times$ be the intersection of the kernel of reduction to $(\mathbb Z/q)^\times$ (the subgroup [`ModularCurve.FullLevel.levelH q M'`](def/ModularCurve_FullLevelJacobian.html#L22)) with the kernel of reduction to $(\mathbb Z/\ell_g)^\times$. Let $p$ be a prime, $k\in\mathbb N$ with $p^k\mid M'$, and $\zeta\in\mathbb C$ a primitive $p^k$-th root of unity. Put $d=$ [`ModularCurve.gamma0PowDeg p k`](def/ModularCurve_WeierstrassGamma0Pow.html#L53), which is $1$ if $p^k=2$ and $\varphi(p^k)/2$ otherwise. The assertion is that for every $j\le d$ there is a modular form $S$ of weight $2(d-j)$ (truncated subtraction, cast to $\mathbb Z$) for the subgroup of $\mathrm{GL}_2(\mathbb R)$ attached to $\Gamma_{H_1}(q^2M')$, namely the image in $\mathrm{SL}_2(\mathbb Z)$ of the matrices of $\Gamma_0(q^2M')$ whose lower-right entry reduces into $H_1$, such that: (i) the $q$-expansion of $S$ of width $1$, viewed as a Laurent series over $\mathbb C$, equals the coefficient of $X^j$ in $\prod (X-(x(\zeta^a)+\tfrac1{12}))$, the product over $1\le a\le p^k/2$ with $p\nmid a$, where $x(c)$ denotes the first component of [`ModularCurve.toricPoint ℂ q c`](def/ModularCurve_TateSlots.html#L125), i.e. the power series with constant term $c/(1-c)^2$ and $m$-th coefficient $\sum_{d\mid m,\ q\mid d}(m/d)\bigl(c^{m/d}+c^{-m/d}\bigr)-2\,[q\mid m]\sum_{e\mid m/q}e$; and (ii) $S\mid_{2(d-j)}\rho^{\sharp}=S$ for every $\rho\in\Gamma_0(M')$, where $\rho^\sharp=$ [`ModularCurve.FullLevel.conjElemN q ρ`](def/ModularCurve_FullLevelLevelAutAt.html#L13) is the real matrix $\begin{pmatrix}a&b/q\\ qc&d\end{pmatrix}$ obtained from $\rho=\begin{pmatrix}a&b\\ c&d\end{pmatrix}$.
--
--   This identifies the coefficients of the recentred kernel polynomial of the $\mu_{p^k}$-generators on the Tate curve with parameter $\mathsf q^{q}$ as $q$-expansions of modular forms on $\Gamma_{H_1}(q^2M')$ that are invariant under the $\mathrm{diag}(q,1)$-conjugates of $\Gamma_0(M')$, the classical mechanism being that $x(\zeta^a)+\tfrac1{12}$ is $(2\pi i)^{-2}\wp(a/p^k;qz)$ and that the elementary symmetric functions of these values are modular of weight $2m$. It is used in the full-level construction, in [`ModularCurve.FullLevel.Diamond.level_fst_act_mapRing_eq_of_curve_eq_units_of_level_fst_rigidDataH1Pow`](thm.html#ModularCurve.FullLevel.Diamond.level_fst_act_mapRing_eq_of_curve_eq_units_of_level_fst_rigidDataH1Pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_exists_modularForm_qExpansion_eq_coeff_toricGenKernel_and_slash_conjElemN_eq.lean

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

theorem ModularCurve.FullLevel.Diamond.exists_modularForm_qExpansion_eq_coeff_toricGenKernel_and_slash_conjElemN_eq
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)

    (p k : ℕ) [Fact p.Prime] (hpk : p ^ k ∣ M') (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (p ^ k)) :
    haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
    ∀ j : ℕ, j ≤ ModularCurve.gamma0PowDeg p k →
      ∃ S : ModularForm (CohCarrier.GammaH (q ^ 2 * M') H₁ :
            Subgroup (GL (Fin 2) ℝ)) (2 * ((ModularCurve.gamma0PowDeg p k - j : ℕ) : ℤ)),
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑S)) =
          (∏ a ∈ (Finset.Icc 1 (p ^ k / 2)).filter (fun a => ¬ p ∣ a),
            (Polynomial.X - Polynomial.C ((ModularCurve.toricPoint ℂ q (ζ ^ a)).1 + HahnSeries.C ((12 : ℂ)⁻¹)))).coeff j ∧
        ∀ ρ : SL(2, ℤ), ρ ∈ CongruenceSubgroup.Gamma0 M' →
          (⇑S ∣[(2 * ((ModularCurve.gamma0PowDeg p k - j : ℕ) : ℤ))] ModularCurve.FullLevel.conjElemN q ρ) = ⇑S := by sorry
