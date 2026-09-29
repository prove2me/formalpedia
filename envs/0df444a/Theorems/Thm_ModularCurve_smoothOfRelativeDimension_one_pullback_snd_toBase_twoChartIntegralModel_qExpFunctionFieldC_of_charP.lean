-- Prove2me | Theorems.Thm_ModularCurve_smoothOfRelativeDimension_one_pullback_snd_toBase_twoChartIntegralModel_qExpFunctionFieldC_of_charP
-- name    : ModularCurve.smoothOfRelativeDimension_one_pullback_snd_toBase_twoChartIntegralModel_qExpFunctionFieldC_of_charP
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/8b78c2c1-1271-5b6b-a2b6-3df3b40c84c6
-- title:
--   Smoothness of the characteristic-p fibre of the two-chart model
-- statement:
--   Fix $M \ge 1$ and a subgroup $\Gamma \le \mathrm{SL}_2(\mathbb{Z})$ with $\Gamma_1(M) \le \Gamma \le \Gamma_0(M)$, and a prime $p$ with $p \nmid M$. Write $F =$ `qExpFunctionFieldC ℚ Γ` for the intermediate field of $\mathbb{Q}((q))$ obtained by adjoining to $\mathbb{Q}$ all quotients $\mathrm{intSeriesC}(p_f)/\mathrm{intSeriesC}(p_g)$ coming from modular forms $f,g$ of a common weight $k$ for $\Gamma$ with integral $q$-expansions $p_f,p_g$ and $\mathrm{intSeriesC}(p_g) \ne 0$, and write $R =$ [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) for the subring of $\mathbb{Q}$ of rationals whose denominator is coprime to $p$. Let $j \in F$ be nonzero (as a `Fact` hypothesis) with Laurent series equal to `jqModC ℚ`, that is $q^{-1}$ times the image in $\mathbb{Q}((q))$ of the power series $E_4^3 \cdot \mathrm{dedekindEtaUnitInv}$. Let $k$ be an algebraically closed field of characteristic $p$ and $\varphi \colon R \to k$ a ring homomorphism. The assertion is that the second projection of the pullback of `TwoChartIntegralModel.toBase R F j` along $\operatorname{Spec} \varphi$ is smooth of relative dimension $1$; here `TwoChartIntegralModel R F j` is the pushout of $\operatorname{Spec}$ of the two inclusions of the $R$-subalgebras `chartAlg R F {j}` and `chartAlg R F {j⁻¹}` of $F$ into the middle ring, and `toBase` is the morphism to $\operatorname{Spec} R$ descended from the $R$-algebra structures of the two charts.
--
--   This is the characteristic-$p$ half of Igusa's good-reduction theorem for $X_H(M)$ at primes not dividing the level: the geometric fibre at $p$ of the two-chart integral model of the field of modular functions for $\Gamma$ with rational $q$-expansions is a smooth curve. It feeds the smoothness conjunct of [`ModularCurve.isProper_and_smooth_and_geometricallyIntegral_twoChartIntegralModel_qExpFunctionFieldC_of_not_dvd`](thm.html#ModularCurve.isProper_and_smooth_and_geometricallyIntegral_twoChartIntegralModel_qExpFunctionFieldC_of_not_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_smoothOfRelativeDimension_one_pullback_snd_toBase_twoChartIntegralModel_qExpFunctionFieldC_of_charP.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve
open AlgebraicCurve

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.smoothOfRelativeDimension_one_pullback_snd_toBase_twoChartIntegralModel_qExpFunctionFieldC_of_charP
    (M : ℕ) [NeZero M] (Γ : Subgroup SL(2, ℤ))
    (hΓ₁ : CongruenceSubgroup.Gamma1 M ≤ Γ) (hΓ₀ : Γ ≤ CongruenceSubgroup.Gamma0 M)
    (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M)
    (j : ↥(qExpFunctionFieldC ℚ Γ)) [Fact (j ≠ 0)] (hj : (j : LaurentSeries ℚ) = jqModC ℚ)
    (k : Type) [Field k] [CharP k p] [IsAlgClosed k] (φ : ↥(GaloisRep.ratLocalizedAt p) →+* k) :
    SmoothOfRelativeDimension 1
      (pullback.snd (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j) (Spec.map (CommRingCat.ofHom φ))) := by sorry
