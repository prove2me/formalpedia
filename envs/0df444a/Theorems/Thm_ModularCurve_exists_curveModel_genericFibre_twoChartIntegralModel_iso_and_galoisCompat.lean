-- Prove2me | Theorems.Thm_ModularCurve_exists_curveModel_genericFibre_twoChartIntegralModel_iso_and_galoisCompat
-- name    : ModularCurve.exists_curveModel_genericFibre_twoChartIntegralModel_iso_and_galoisCompat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/51ff509d-7217-5fca-8057-80620f96ef5a
-- title:
--   Geometric generic fibre of the two-chart integral model
-- statement:
--   Let $F_0$ be an intermediate field of $\mathbb{Q}$ in the Laurent series field $\mathbb{Q}((q))$, let $p$ be a prime, and let $j \in F_0$ be nonzero and transcendental over $\mathbb{Q}$, with $F_0$ finite-dimensional over $\mathbb{Q}(j)$. Write $\mathbb{Z}_{(p)} =$ [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8), the subring of rationals whose denominator is coprime to $p$, and let $\overline{\mathbb{Q}}\cdot F_0 =$ `laurentBaseChange (AlgebraicClosure ℚ) F₀` be the subfield of $\overline{\mathbb{Q}}((q))$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise image of $F_0$. The assertion is that there exist a `CurveModel` $M_\eta$ for $\overline{\mathbb{Q}} \subseteq \overline{\mathbb{Q}}\cdot F_0$ — that is, an integral scheme $M_\eta.C$ with a proper, smooth of relative dimension $1$ morphism $M_\eta.\mathrm{toBase}$ to $\operatorname{Spec} \overline{\mathbb{Q}}$, a ring isomorphism of $\overline{\mathbb{Q}}\cdot F_0$ with the function field of $M_\eta.C$ compatible with the structure map on $\overline{\mathbb{Q}}$, a bijection of the closed points of $M_\eta.C$ with the places of $\overline{\mathbb{Q}}\cdot F_0$ over $\overline{\mathbb{Q}}$ (valuation subrings, not the whole field, containing $\overline{\mathbb{Q}}$ and principal), matching each local ring with the corresponding valuation subring, and such that every finite set of points lies in an affine open — together with an isomorphism $e_\eta$ from $M_\eta.C$ to the pullback of `TwoChartIntegralModel.toBase` $\mathbb{Z}_{(p)}\,F_0\,j$ along $\operatorname{Spec}\overline{\mathbb{Q}} \to \operatorname{Spec}\mathbb{Z}_{(p)}$, here the scheme glued from the spectra of the chart algebras `chartAlgFin` and `chartAlgInf` over its structure morphism to $\operatorname{Spec}\mathbb{Z}_{(p)}$, such that: $e_\eta$ followed by the second projection is $M_\eta.\mathrm{toBase}$; and for every $\sigma \in \operatorname{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$ and all sections $x, x'$ of $M_\eta.\mathrm{toBase}$, if the composite of $x'$ with $e_\eta$ and the first projection equals $\operatorname{Spec}(\sigma)$ followed by that composite for $x$, then `Mη.pointEquivPlace x'` is the image of `Mη.pointEquivPlace x` under the action of the semilinear automorphism `arithmeticGalois F₀ σ`, which acts on $\overline{\mathbb{Q}}\cdot F_0$ by $\sigma$ on the coefficients of $q$-expansions.
--
--   This identifies the geometric generic fibre of the normalisation of the $j$-line over $\mathbb{Z}_{(p)}$ in a field $F_0$ of $q$-expansions as a smooth proper model of $\overline{\mathbb{Q}}\cdot F_0$ over $\overline{\mathbb{Q}}$, with the identification of closed points with places compatible with the coefficientwise Galois action. It feeds [`ModularCurve.exists_smoothProperModel_qExpFunctionField_genericFibre_galoisCompat_of_not_dvd`](thm.html#ModularCurve.exists_smoothProperModel_qExpFunctionField_genericFibre_galoisCompat_of_not_dvd), the step providing integral models of modular curves together with the Galois action on their geometric points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_curveModel_genericFibre_twoChartIntegralModel_iso_and_galoisCompat.lean

import Mathlib
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_curveModel_genericFibre_twoChartIntegralModel_iso_and_galoisCompat
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (p : ℕ) [Fact p.Prime]
    (j : ↥F₀) [Fact (j ≠ 0)] (hj : Transcendental ℚ j)
    [FiniteDimensional ↥(IntermediateField.adjoin ℚ ({j} : Set ↥F₀)) ↥F₀] :
    ∃ (Mη : CurveModel (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))
      (eη : Mη.C ⟶ pullback (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j)
        (Spec.map (CommRingCat.ofHom
          (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))))) (_ : IsIso eη),
      eη ≫ pullback.snd (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) _ =
        Mη.toBase ∧
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (x x' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
        x'.1 ≫ eη ≫ pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) _ =
          Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
            x.1 ≫ eη ≫
              pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) _ →
        Mη.pointEquivPlace x' =
          arithmeticGalois (L := AlgebraicClosure ℚ) F₀ σ • Mη.pointEquivPlace x := by sorry
