-- Prove2me | Theorems.Thm_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat
-- name    : ModularCurve.exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/9506a8ce-01b3-599a-a235-89de80f46f82
-- title:
--   Generic fibre of the two-chart integral model, with Galois compatibility
-- statement:
--   Let $F_0$ be an intermediate field of $\mathbb Q$ in $\mathbb Q((q))$, let $p$ be a prime, write $\mathbb Z_{(p)}=$ [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) for the subring of rationals whose denominator is coprime to $p$, and let $j \in F_0$ be nonzero. Let $\overline{\mathbb Q}F_0 =$ `laurentBaseChange (AlgebraicClosure ℚ) F₀` be the subfield of $\overline{\mathbb Q}((q))$ generated over $\overline{\mathbb Q}$ by the coefficientwise image `coeffEmb` of $F_0$, and let $\bar\jmath$ be an element of it with $\bar\jmath =$ `coeffEmb` $(j)$, nonzero and transcendental over $\overline{\mathbb Q}$, and such that $\overline{\mathbb Q}F_0$ is finite over $\overline{\mathbb Q}(\bar\jmath)$ and over $\overline{\mathbb Q}(\bar\jmath^{-1})$. Assume given $\overline{\mathbb Q}$-algebra isomorphisms $e_{\mathrm{fin}}\colon \overline{\mathbb Q}\otimes_{\mathbb Z_{(p)}}A_{\mathrm{fin}} \to R_{\mathrm{fin}}$ and $e_\infty\colon \overline{\mathbb Q}\otimes_{\mathbb Z_{(p)}}A_\infty \to R_\infty$, where $A_{\mathrm{fin}} =$ `chartAlgFin` and $A_\infty =$ `chartAlgInf` are the subalgebras of $F_0$ attached over $\mathbb Z_{(p)}$ to $\{j\}$ and $\{j^{-1}\}$, and $R_{\mathrm{fin}}$, $R_\infty$ are the integral closures in $\overline{\mathbb Q}F_0$ of $\overline{\mathbb Q}[\bar\jmath]$, respectively $\overline{\mathbb Q}[\bar\jmath^{-1}]$, and assume that on elements $1 \otimes b$ both isomorphisms are given by the coefficientwise embedding of $b \in F_0$. Let $M_\eta =$ `CurveModel.ofGenerator` $(\overline{\mathbb Q}, \bar\jmath)$ be the resulting curve model: an integral scheme, proper and smooth of relative dimension $1$ over $\operatorname{Spec}\overline{\mathbb Q}$, with function field identified with $\overline{\mathbb Q}F_0$ over $\overline{\mathbb Q}$ and closed points in bijection with the places of $\overline{\mathbb Q}F_0$ over $\overline{\mathbb Q}$. Then there is a morphism $e_\eta$ from $M_\eta.C$ to the pullback of the structure morphism `TwoChartIntegralModel.toBase` $\mathbb Z_{(p)}\,F_0\,j$ along $\operatorname{Spec}$ of $\mathbb Z_{(p)} \to \overline{\mathbb Q}$, together with a proof that $e_\eta$ is an isomorphism, such that: $e_\eta$ followed by the second projection is $M_\eta.\mathrm{toBase}$; the finite chart immersion `CurveModel.ι₀` of $M_\eta$ followed by $e_\eta$ and the first projection equals $\operatorname{Spec}$ of the ring map $e_{\mathrm{fin}} \circ (b \mapsto 1\otimes b)$ followed by the chart immersion `TwoChartIntegralModel.ιFin`, and likewise with `CurveModel.ιInf`, $e_\infty$ and `TwoChartIntegralModel.ιInf`; and, for every $\mathbb Q$-algebra automorphism $\sigma$ of $\overline{\mathbb Q}$ and all $\overline{\mathbb Q}$-points $x,x'$ of $M_\eta$ (sections of $M_\eta.\mathrm{toBase}$), if $x'$ followed by $e_\eta$ and the first projection equals $\operatorname{Spec}\sigma$ followed by the same composite for $x$, then the place attached to $x'$ by `pointEquivPlace` is the image of the place attached to $x$ under the action of the semilinear automorphism `arithmeticGalois` $F_0\,\sigma$ of $\overline{\mathbb Q}F_0$ over $\sigma$.
--
--   This identifies the generic fibre, i.e. the base change to $\overline{\mathbb Q}$, of the two-chart integral model over $\mathbb Z_{(p)}$ of a field of $q$-expansions with the glued smooth proper $\overline{\mathbb Q}$-curve attached to the generator $\bar\jmath$, pinning the isomorphism on both charts and recording that it transports the Galois action on $\overline{\mathbb Q}$-points to the coefficientwise action on places in the sense of Shimura's arithmetic theory. It is used by the statements assembling a curve model of the modular curve together with its integral model over $\mathbb Z_{(p)}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_CurveModelConstruction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve
open scoped TensorProduct
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (p : ℕ) [Fact p.Prime] (j : ↥F₀) [Fact (j ≠ 0)]
    (jb : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))
    (hjb : (jb : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) ((j : ↥F₀) : LaurentSeries ℚ))
    (htrans : Transcendental (AlgebraicClosure ℚ) jb)
    [hne : Fact (jb ≠ 0)]
    [hfd : FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({jb} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))) ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)]
    [hfd_inv : FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({jb⁻¹} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))) ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)]
    (eFin : (AlgebraicClosure ℚ) ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j)
        ≃ₐ[AlgebraicClosure ℚ] ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({jb} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))))
    (hFin : ∀ b : ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j),
        ((eFin (1 ⊗ₜ b) : ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({jb} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)))) : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)) =
          (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥F₀) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b : ↥F₀).2⟩ : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)))
    (eInf : (AlgebraicClosure ℚ) ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j)
        ≃ₐ[AlgebraicClosure ℚ] ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({jb⁻¹} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))))
    (hInf : ∀ b : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j),
        ((eInf (1 ⊗ₜ b) : ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({jb⁻¹} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)))) : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)) =
          (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥F₀) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b : ↥F₀).2⟩ : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))) :
    let Mη : CurveModel (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀) :=
      CurveModel.ofGenerator (AlgebraicClosure ℚ) jb htrans
    ∃ (eη : Mη.C ⟶ pullback (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) (Spec.map (CommRingCat.ofHom
        (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))))) (_ : IsIso eη),
      eη ≫ pullback.snd (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) _ = Mη.toBase ∧
      (AlgebraicCurve.CurveModel.ι₀ (AlgebraicClosure ℚ) jb ≫ eη ≫ pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) _ =
        Spec.map (CommRingCat.ofHom (eFin.toAlgHom.toRingHom.comp
          (Algebra.TensorProduct.includeRight
            (R := ↥(GaloisRep.ratLocalizedAt p)) (A := AlgebraicClosure ℚ) (B := ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j))).toRingHom)) ≫
          TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) ∧
      (AlgebraicCurve.CurveModel.ιInf (AlgebraicClosure ℚ) jb ≫ eη ≫ pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) _ =
        Spec.map (CommRingCat.ofHom (eInf.toAlgHom.toRingHom.comp
          (Algebra.TensorProduct.includeRight
            (R := ↥(GaloisRep.ratLocalizedAt p)) (A := AlgebraicClosure ℚ) (B := ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j))).toRingHom)) ≫
          TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) ∧
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (x x' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
        x'.1 ≫ eη ≫ pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) _ =
          Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ x.1 ≫ eη ≫ pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) _ →
        Mη.pointEquivPlace x' =
          arithmeticGalois (L := AlgebraicClosure ℚ) F₀ σ • Mη.pointEquivPlace x := by sorry
