-- Prove2me | Theorems.Thm_ModularCurve_exists_ringEquiv_functionField_pullback_comp_baseToFunctionField_eq_and_germToFunctionField_eq_chartMap_of_neZero
-- name    : ModularCurve.exists_ringEquiv_functionField_pullback_comp_baseToFunctionField_eq_and_germToFunctionField_eq_chartMap_of_neZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/7bd6e307-f250-52b6-8ced-5a01382280a7
-- title:
--   Function field of the geometric generic fibre is ℚ̄F_N
-- statement:
--   Fix $N\ge 1$ and a prime $p$, and let $R=$ [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) be the subring of $\mathbf Q$ of rationals whose denominator is coprime to $p$. Let $c : X \to \operatorname{Spec} R$ be a morphism of schemes with $X$ integral, $c$ proper and smooth of relative dimension $1$, and let $\mathcal V$ be a two-chart affine open cover of $X$: affine opens $U_0,U_1$ with $U_0\sqcup U_1=\top$ and $U_0\cap U_1$ affine; write $A_0=\Gamma(X,U_0)$. Suppose given a ring homomorphism $\iota : A_0 \to \overline{F}_N$, where $\overline{F}_N$ is `modularFunctionFieldBar N`, the base change to $\mathrm{LaurentSeries}(\overline{\mathbf Q})$ of the subfield $F_N=\mathbf Q(\text{divisorExpansions } N)$ of $\mathrm{LaurentSeries}(\mathbf Q)$, such that: $\iota$ is $R$-linear, in the sense that $\iota$ composed with $R\to A_0$ equals $R\to\overline{\mathbf Q}\to\overline{F}_N$; $\iota$ is injective; every $\iota(a)$ equals the coefficientwise image `coeffEmb` of some element of $F_N$; and every $x\in F_N$ is a fraction of values of $\iota$, i.e. there are $a,b\in A_0$ with $\iota b\neq 0$ and $\mathrm{coeffEmb}(x)\cdot \iota b=\iota a$. Assume further that the pullback $X_{\overline{\mathbf Q}}$ of $c$ along $\operatorname{Spec}\overline{\mathbf Q}\to\operatorname{Spec} R$ is integral and that the chart $U_0$ of the pulled-back cover is nonempty. Then there is a ring isomorphism $\Phi$ from the function field of $X_{\overline{\mathbf Q}}$ onto $\overline{F}_N$ such that $\Phi$ composed with `baseToFunctionField` for the structure morphism $X_{\overline{\mathbf Q}}\to\operatorname{Spec}\overline{\mathbf Q}$ (the germ at the generic point of the image of a scalar) is the inclusion $\overline{\mathbf Q}\to\overline{F}_N$, and such that for every $a\in A_0$ the image under $\Phi$ of the germ at the generic point of the pullback of $a$ along the first projection, taken on the chart $U_0$ of the pulled-back cover, equals $\iota(a)$.
--
--   This identifies the function field of the geometric generic fibre of an arithmetic model over $\mathbf Z_{(p)}$ with the modular function field $\overline{F}_N$ over $\overline{\mathbf Q}$, compatibly with the chart embedding $\iota$, the birational comparison between an abstract curve over $\mathbf Z_{(p)}$ and $X_0(N)$ presented by $q$-expansions. It is used in the transfer of regular differentials across this identification, namely by [`ModularCurve.res_mem_regularDifferentialsBar_of_chartMap_of_neZero`](thm.html#ModularCurve.res_mem_regularDifferentialsBar_of_chartMap_of_neZero) and [`ModularCurve.mem_span_range_res_of_mem_regularDifferentialsBar_of_chartMap_of_neZero`](thm.html#ModularCurve.mem_span_range_res_of_mem_regularDifferentialsBar_of_chartMap_of_neZero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_ringEquiv_functionField_pullback_comp_baseToFunctionField_eq_and_germToFunctionField_eq_chartMap_of_neZero.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler
import Definitions.Def_AlgebraicCurve_KaehlerToFunctionField

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve

theorem ModularCurve.exists_ringEquiv_functionField_pullback_comp_baseToFunctionField_eq_and_germToFunctionField_eq_chartMap_of_neZero
    (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))) [IsIntegral X] [IsProper c]
    [SmoothOfRelativeDimension 1 c] (𝒱 : X.TwoAffineOpenCover)
    (ι : (𝒱.cover c).A0 →+* ↥(modularFunctionFieldBar N))
    (hιR : ι.comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) (𝒱.cover c).A0) =
      (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))
    (hιinj : Function.Injective ι)
    (hιrat : ∀ a : (𝒱.cover c).A0, ∃ x ∈ modularFunctionFieldFull N,
      coeffEmb (AlgebraicClosure ℚ) x = (ι a : LaurentSeries (AlgebraicClosure ℚ)))
    (hιfrac : ∀ x ∈ modularFunctionFieldFull N, ∃ a b : (𝒱.cover c).A0, ι b ≠ 0 ∧
      coeffEmb (AlgebraicClosure ℚ) x * (ι b : LaurentSeries (AlgebraicClosure ℚ)) = ι a)
    [IsIntegral (pullback c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))] [Nonempty (𝒱.pullback c (AlgebraicClosure ℚ)).U0] :
    ∃ Φ : (pullback c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))).functionField ≃+* ↥(modularFunctionFieldBar N),
      Φ.toRingHom.comp (baseToFunctionField (pullback.snd c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))) = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) ∧
      ∀ a : (𝒱.cover c).A0,
        Φ (((pullback c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))).germToFunctionField (𝒱.pullback c (AlgebraicClosure ℚ)).U0).hom
          ((Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c (AlgebraicClosure ℚ)).ringHom0 a)) = ι a := by sorry
