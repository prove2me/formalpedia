-- Prove2me | Theorems.Thm_ModularCurve_exists_ringHom_cover_modularFunctionFieldBar_of_ratCurveModel_of_neZero
-- name    : ModularCurve.exists_ringHom_cover_modularFunctionFieldBar_of_ratCurveModel_of_neZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/470b76fb-710f-551f-a3b6-9b94a0c51cdd
-- title:
--   Chart rings of a mathbf Z₍ₚ₎-model embed into ̄ F_N
-- statement:
--   Fix $N\ge 1$ and a prime $p$, and write $R=$ [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) for the subring of $\mathbf Q$ of rationals whose denominator is coprime to $p$. Let $X$ be an integral scheme with a morphism $c\colon X\to\operatorname{Spec}R$ and a two-chart affine open cover $\mathcal V$, i.e. affine opens $U_0,U_1$ with $U_0\sqcup U_1=\top$ and $U_0\cap U_1$ affine; set $A_0=\Gamma(X,U_0)$, $A_{01}=\Gamma(X,U_0\cap U_1)$, these being the chart rings of `𝒱.cover c`, with their $R$-algebra structures coming from $c$ and $\rho_0\colon A_0\to A_{01}$ the restriction. Let $M_0$ be a `CurveModel` of $F_N=$ `modularFunctionFieldFull N` $=\mathbf Q(\mathrm{divisorExpansions}\,N)\subset\mathbf Q((q))$ over $\mathbf Q$: an integral scheme $M_0.C$, proper and smooth of relative dimension $1$ over $\operatorname{Spec}\mathbf Q$, with a ring isomorphism $\mathrm{ffEquiv}\colon F_N\to\mathbf Q(M_0.C)$ over $\mathbf Q$, a bijection from the closed points onto the places of $F_N/\mathbf Q$ matching stalks with valuation subrings, and every finite set of points contained in an affine open. Let $e_0\colon M_0.C\to X\times_{\operatorname{Spec}R}\operatorname{Spec}\mathbf Q$ be an isomorphism commuting with the structure maps to $\operatorname{Spec}\mathbf Q$ ($e_0$ followed by the second projection is $M_0.\mathrm{toBase}$), and assume the generic point of $M_0.C$ lies in the preimage of $U_0$, and in that of $U_0\cap U_1$, under $e_0$ followed by the first projection $\mathrm{pr}_1$. Then there are ring homomorphisms $\iota\colon A_0\to\bar F_N$ and $\iota_{01}\colon A_{01}\to\bar F_N$, where $\bar F_N=$ `modularFunctionFieldBar N` is the base change of $F_N$ inside $\bar{\mathbf Q}((q))$, such that: on each of $U_0$ and $U_0\cap U_1$, the image of $\iota$ (resp. $\iota_{01}$) in $\bar{\mathbf Q}((q))$ is computed by pulling a section back along $e_0$ followed by $\mathrm{pr}_1$, taking its germ at the generic point of $M_0.C$, transporting through $\mathrm{ffEquiv}^{-1}$ into $F_N\subset\mathbf Q((q))$ and applying the coefficientwise embedding `coeffEmb`; $\iota_{01}\circ\rho_0=\iota$; both $\iota$ and $\iota_{01}$ restrict on $R$ to $R\to\bar{\mathbf Q}\to\bar F_N$; both are injective; every value $\iota(a)$ lies in the image of $F_N$ under `coeffEmb`; and every $x\in F_N$ satisfies $\mathrm{coeffEmb}(x)\cdot\iota(b)=\iota(a)$ for some $a,b\in A_0$ with $\iota(b)\ne 0$.
--
--   This identifies the coordinate rings of the two charts of an integral $\mathbf Z_{(p)}$-scheme whose generic fibre is a given rational model of the modular function field of level $N$ with subrings of $\bar{\mathbf Q}((q))$, generating the function field as a field of fractions; the argument uses only that $R$ is a discrete valuation ring with fraction field $\mathbf Q$. It is the comparison step underlying the level-$N$ statements on base change of $H^0$ of Kähler differentials, on $q$-expansions of integral differentials, and on points of the relative Jacobian over the dual numbers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_ringHom_cover_modularFunctionFieldBar_of_ratCurveModel_of_neZero.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve

theorem ModularCurve.exists_ringHom_cover_modularFunctionFieldBar_of_ratCurveModel_of_neZero
    (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))) [IsIntegral X] (𝒱 : X.TwoAffineOpenCover)
    (M₀ : CurveModel ℚ ↥(modularFunctionFieldFull N))
    (e₀ : M₀.C ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)))) [IsIso e₀]
    (he₀ : e₀ ≫ pullback.snd c _ = M₀.toBase)
    (hgen0 : genericPoint M₀.C ∈ (e₀ ≫ pullback.fst c _) ⁻¹ᵁ 𝒱.U0)
    (hgen01 : genericPoint M₀.C ∈ (e₀ ≫ pullback.fst c _) ⁻¹ᵁ (𝒱.U0 ⊓ 𝒱.U1)) :
    ∃ (ι : (𝒱.cover c).A0 →+* ↥(modularFunctionFieldBar N)) (ι₀₁ : (𝒱.cover c).A01 →+* ↥(modularFunctionFieldBar N)),

      (∀ a : (𝒱.cover c).A0, ((ι a : ↥(modularFunctionFieldBar N)) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) (((M₀.ffEquiv.symm ((M₀.C.presheaf.germ ((e₀ ≫ pullback.fst c _) ⁻¹ᵁ 𝒱.U0) (genericPoint M₀.C) hgen0).hom (((e₀ ≫ pullback.fst c _).app (𝒱.U0)).hom a))) : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ)) ∧
      (∀ a : (𝒱.cover c).A01, ((ι₀₁ a : ↥(modularFunctionFieldBar N)) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) (((M₀.ffEquiv.symm ((M₀.C.presheaf.germ ((e₀ ≫ pullback.fst c _) ⁻¹ᵁ (𝒱.U0 ⊓ 𝒱.U1)) (genericPoint M₀.C) hgen01).hom (((e₀ ≫ pullback.fst c _).app (𝒱.U0 ⊓ 𝒱.U1)).hom a))) : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ)) ∧
      (∀ a : (𝒱.cover c).A0, ι₀₁ ((𝒱.cover c).ρ0 a) = ι a) ∧

      ι.comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) (𝒱.cover c).A0) =
        (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) ∧
      ι₀₁.comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) (𝒱.cover c).A01) =
        (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) ∧

      Function.Injective ι ∧ Function.Injective ι₀₁ ∧

      (∀ a : (𝒱.cover c).A0, ∃ x ∈ modularFunctionFieldFull N,
        coeffEmb (AlgebraicClosure ℚ) x = (ι a : LaurentSeries (AlgebraicClosure ℚ))) ∧

      (∀ x ∈ modularFunctionFieldFull N, ∃ a b : (𝒱.cover c).A0, ι b ≠ 0 ∧
        coeffEmb (AlgebraicClosure ℚ) x * (ι b : LaurentSeries (AlgebraicClosure ℚ)) = ι a) := by sorry
