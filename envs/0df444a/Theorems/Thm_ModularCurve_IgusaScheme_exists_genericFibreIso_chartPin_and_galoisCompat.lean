-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_exists_genericFibreIso_chartPin_and_galoisCompat
-- name    : ModularCurve.IgusaScheme.exists_genericFibreIso_chartPin_and_galoisCompat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/2acee47d-0436-554d-9913-118a92a0b131
-- title:
--   Galois-compatible generic fibre isomorphism for the Igusa scheme
-- statement:
--   Fix a level $N \ge 1$ and a prime $\ell$ with $\ell \nmid N$, and write $\mathbb{Z}_{(\ell)}$ for the subring [`GaloisRep.ratLocalizedAt ℓ`](def/GaloisRep_Flat.html#L8) of rationals whose denominator is coprime to $\ell$. Inside $\bar{\mathbb{Q}}((q))$ let $\bar F_N :=$ `modularFunctionFieldBar N` be the base change to $\bar{\mathbb{Q}}$ of the field `modularFunctionFieldFull N` $= \mathbb{Q}(\text{divisorExpansions } N)$, and let $\bar\jmath :=$ `jBar N` be the coefficientwise image of the $q$-expansion of $j$ in $\bar F_N$. Assume $\bar\jmath$ is transcendental over $\bar{\mathbb{Q}}$, that $\bar\jmath \neq 0$, and that $\bar F_N$ is finite-dimensional over $\bar{\mathbb{Q}}(\bar\jmath)$ and over $\bar{\mathbb{Q}}(\bar\jmath^{-1})$. Assume further given $\bar{\mathbb{Q}}$-algebra isomorphisms $e_{\mathrm{fin}} : \bar{\mathbb{Q}} \otimes_{\mathbb{Z}_{(\ell)}} A_{\mathrm{fin}} \to \mathcal{O}_{\mathrm{fin}}$ and $e_{\inf} : \bar{\mathbb{Q}} \otimes_{\mathbb{Z}_{(\ell)}} A_{\inf} \to \mathcal{O}_{\inf}$, where $A_{\mathrm{fin}} =$ `chartAlgFin N ℓ`, $A_{\inf} =$ `chartAlgInf N ℓ` are the two Igusa chart algebras over $\mathbb{Z}_{(\ell)}$ inside `modularFunctionFieldFull N`, and $\mathcal{O}_{\mathrm{fin}}$, $\mathcal{O}_{\inf}$ are the subalgebras `CurveModel.chartRing` of $\bar F_N$ of elements integral over $\bar{\mathbb{Q}}[\bar\jmath]$, resp. over $\bar{\mathbb{Q}}[\bar\jmath^{-1}]$; the hypotheses $h_{\mathrm{fin}}$, $h_{\inf}$ require that $e_{\mathrm{fin}}(1 \otimes b)$, resp. $e_{\inf}(1 \otimes b)$, is the coefficientwise embedding `coeffEmb` of $b$ into $\bar{\mathbb{Q}}((q))$. Put $M_\eta :=$ `CurveModel.ofGenerator` $\bar{\mathbb{Q}}\,\bar\jmath$, the glued two-chart proper smooth relative-dimension-one model of $\bar F_N$ over $\bar{\mathbb{Q}}$ attached to the generator $\bar\jmath$. Then there is a morphism $e_\eta$ from $M_\eta.C$ to the fibre product of `igusaTo N ℓ` $:$ `IgusaScheme N ℓ` $\to \operatorname{Spec}\mathbb{Z}_{(\ell)}$ with $\operatorname{Spec}\bar{\mathbb{Q}} \to \operatorname{Spec}\mathbb{Z}_{(\ell)}$, which is an isomorphism, such that: $e_\eta$ followed by the second projection is $M_\eta.\mathrm{toBase}$; the chart morphism `CurveModel.ι₀` followed by $e_\eta$ and the first projection equals $\operatorname{Spec}$ of $e_{\mathrm{fin}} \circ \mathrm{includeRight}$ followed by the chart morphism `ιFin N ℓ`, and likewise with `ιInf`, $e_{\inf}$ and [`ModularCurve.IgusaScheme.ιInf N ℓ`](def/ModularCurve_IgusaScheme.html#L259); and, for every $g \in \mathrm{Gal}(\bar{\mathbb{Q}}/\mathbb{Q})$ and any two $\bar{\mathbb{Q}}$-points $x, x'$ of $M_\eta.C$ (sections of $M_\eta.\mathrm{toBase}$), if the composite of $x'$ with $e_\eta$ and the first projection equals $\operatorname{Spec}(g)$ followed by that of $x$, then $M_\eta.\mathrm{pointEquivPlace}(x')$ is the translate of $M_\eta.\mathrm{pointEquivPlace}(x)$ under the action of the semilinear automorphism `arithmeticGalois` $(\text{modularFunctionFieldFull } N)\,g$ on places of $\bar F_N$ over $\bar{\mathbb{Q}}$.
--
--   This identifies the generic fibre of the two-chart Igusa scheme over $\mathbb{Z}_{(\ell)}$ with the abstract curve model of the modular function field $\bar{\mathbb{Q}}(X_0(N))$, pinning the identification chart by chart and recording that it intertwines the Galois action on $\bar{\mathbb{Q}}$-points with the arithmetic Galois action on places. It feeds the Deligne–Rapoport-style relative model package, where the comparison of generic-fibre points with places and the compatibility of the two reduction maps are established.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_exists_genericFibreIso_chartPin_and_galoisCompat.lean

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_FibreModel
import Definitions.Def_AlgebraicCurve_CurveModelConstruction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
  ModularCurve AlgebraicCurve ModularCurve.IgusaScheme ModularCurve.CharPModel

open scoped TensorProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.IgusaScheme.exists_genericFibreIso_chartPin_and_galoisCompat
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (htrans : Transcendental (AlgebraicClosure ℚ) (jBar N))
    [hne : Fact (jBar N ≠ 0)]
    [hfd : FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({jBar N} : Set (modularFunctionFieldBar N)))
      (modularFunctionFieldBar N)]
    [hfd_inv : FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({(jBar N)⁻¹} : Set (modularFunctionFieldBar N)))
      (modularFunctionFieldBar N)]
    (eFin : (AlgebraicClosure ℚ) ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgFin N ℓ)
        ≃ₐ[AlgebraicClosure ℚ]
      ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ)
        ({jBar N} : Set (modularFunctionFieldBar N))))
    (hFin : ∀ b : chartAlgFin N ℓ, ((eFin (1 ⊗ₜ b) :
        ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ)
        ({jBar N} : Set (modularFunctionFieldBar N)))) : modularFunctionFieldBar N)
      = (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (b : ↥(modularFunctionFieldFull N)).2⟩ : modularFunctionFieldBar N))
    (eInf : (AlgebraicClosure ℚ) ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgInf N ℓ)
        ≃ₐ[AlgebraicClosure ℚ]
      ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ)
        ({(jBar N)⁻¹} : Set (modularFunctionFieldBar N))))
    (hInf : ∀ b : chartAlgInf N ℓ, ((eInf (1 ⊗ₜ b) :
        ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ)
        ({(jBar N)⁻¹} : Set (modularFunctionFieldBar N)))) : modularFunctionFieldBar N)
      = (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (b : ↥(modularFunctionFieldFull N)).2⟩ : modularFunctionFieldBar N)) :
    let Mη : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
      CurveModel.ofGenerator (AlgebraicClosure ℚ) (jBar N) htrans
    ∃ (eη : Mη.C ⟶ pullback (igusaTo N ℓ) (Spec.map (CommRingCat.ofHom
        (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))))) (_ : IsIso eη),
      eη ≫ pullback.snd (igusaTo N ℓ) _ = Mη.toBase ∧
      (AlgebraicCurve.CurveModel.ι₀ (AlgebraicClosure ℚ) (jBar N) ≫ eη ≫
        pullback.fst (igusaTo N ℓ) _ =
      Spec.map (CommRingCat.ofHom (eFin.toAlgHom.toRingHom.comp
        (Algebra.TensorProduct.includeRight
          (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := AlgebraicClosure ℚ)
          (B := ↥(chartAlgFin N ℓ))).toRingHom)) ≫ ModularCurve.IgusaScheme.ιFin N ℓ) ∧
      (AlgebraicCurve.CurveModel.ιInf (AlgebraicClosure ℚ) (jBar N) ≫ eη ≫
        pullback.fst (igusaTo N ℓ) _ =
      Spec.map (CommRingCat.ofHom (eInf.toAlgHom.toRingHom.comp
        (Algebra.TensorProduct.includeRight
          (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := AlgebraicClosure ℚ)
          (B := ↥(chartAlgInf N ℓ))).toRingHom)) ≫ ModularCurve.IgusaScheme.ιInf N ℓ) ∧
      ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (x x' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
        x'.1 ≫ eη ≫ pullback.fst (igusaTo N ℓ) _ =
          Spec.map (CommRingCat.ofHom (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
            x.1 ≫ eη ≫ pullback.fst (igusaTo N ℓ) _ →
        Mη.pointEquivPlace x' =
          arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) g •
            Mη.pointEquivPlace x := by sorry
