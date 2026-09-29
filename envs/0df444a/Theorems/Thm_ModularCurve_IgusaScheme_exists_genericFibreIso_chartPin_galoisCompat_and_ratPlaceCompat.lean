-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_exists_genericFibreIso_chartPin_galoisCompat_and_ratPlaceCompat
-- name    : ModularCurve.IgusaScheme.exists_genericFibreIso_chartPin_galoisCompat_and_ratPlaceCompat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/ddd4c2fc-2235-5532-ba9a-c3de4681521e
-- title:
--   Generic fibres of the Igusa model: chart pins, Galois and place compatibility
-- statement:
--   Fix $N \ge 1$ and a prime $\ell$ with $\ell \nmid N$. Write $F_0 = \mathbb{Q}(\mathrm{divisorExpansions}\,N) \subset \mathbb{Q}((q))$ for `modularFunctionFieldFull N`, $\bar F_0 =$ `modularFunctionFieldBar N` for its coefficientwise base change to $\bar{\mathbb{Q}}$, $j_{\mathrm{full}} \in F_0$ and $\bar j \in \bar F_0$ for the $q$-expansion of $j$ at the two levels, and $\mathbb{Z}_{(\ell)}$ for [`GaloisRep.ratLocalizedAt ℓ`](def/GaloisRep_Flat.html#L8), the rationals with denominator coprime to $\ell$. Assumed: $\bar j$ transcendental over $\bar{\mathbb{Q}}$, $\bar j \ne 0$, and $\bar F_0$ finite over $\bar{\mathbb{Q}}(\bar j)$ and over $\bar{\mathbb{Q}}(\bar j^{-1})$; $\bar{\mathbb{Q}}$-algebra isomorphisms $e_{\mathrm{Fin}}, e_{\mathrm{Inf}}$ from $\bar{\mathbb{Q}} \otimes_{\mathbb{Z}_{(\ell)}}$ `chartAlgFin N ℓ`, resp. `chartAlgInf N ℓ`, onto the integral closure in $\bar F_0$ of $\bar{\mathbb{Q}}[\bar j]$, resp. $\bar{\mathbb{Q}}[\bar j^{-1}]$, each sending $1 \otimes b$ to the coefficientwise image of $b$; and the same data over $\mathbb{Q}$ for $j_{\mathrm{full}}$ ($e_{\mathrm{Fin},0}, e_{\mathrm{Inf},0}$ sending $1 \otimes b$ to $b$). Let $M_\eta =$ `CurveModel.ofGenerator` $\bar{\mathbb{Q}}\,\bar j$ and $M_0 =$ `CurveModel.ofGenerator` $\mathbb{Q}\,j_{\mathrm{full}}$ be the glued two-chart smooth proper curve models. The conclusion asserts the existence of an isomorphism $e_\eta$ from $M_\eta.C$ to the fibre product of `igusaTo N ℓ` with $\operatorname{Spec} \bar{\mathbb{Q}} \to \operatorname{Spec} \mathbb{Z}_{(\ell)}$, compatible with the structure morphisms to $\operatorname{Spec} \bar{\mathbb{Q}}$, whose composite with the first projection restricts on the two charts $\iota_0$, $\iota_\infty$ to the spectra of $e_{\mathrm{Fin}}$, $e_{\mathrm{Inf}}$ precomposed with the right inclusion, followed by `ιFin N ℓ`, resp. `ιInf N ℓ`; such that for all $g \in \operatorname{Gal}(\bar{\mathbb{Q}}/\mathbb{Q})$ and all $\bar{\mathbb{Q}}$-points $x, x'$ of $M_\eta$ (sections of $M_\eta.\mathrm{toBase}$), if the image of $x'$ in the Igusa scheme equals $\operatorname{Spec}(g)$ followed by that of $x$, then `pointEquivPlace` $x'$ is the `arithmeticGalois` image of $g$ acting on `pointEquivPlace` $x$; and, in the same existential, the existence of an analogous isomorphism $e_0$ from $M_0.C$ onto the fibre product of `igusaTo N ℓ` with $\operatorname{Spec} \mathbb{Q}$, over $\mathbb{Q}$ and pinned on both charts by $e_{\mathrm{Fin},0}$, $e_{\mathrm{Inf},0}$, satisfying: for every $\bar{\mathbb{Q}}$-point $x$ of $M_\eta$, every $\bar{\mathbb{Q}}$-point $y$ of that $\mathbb{Q}$-fibre product and every closed point $x_0$ of $M_0.C$, if $y$ and $x$ have the same image in the Igusa scheme and $y$ followed by $e_0^{-1}$ sends the closed point of $\operatorname{Spec}\bar{\mathbb{Q}}$ to $x_0$, then the valuation subring of `pointEquivPlace` $x$, pulled back along $F_0 \to \bar{\mathbb{Q}} \otimes_{\mathbb{Q}} F_0 \xrightarrow{\ \sim\ } \bar F_0$, equals the valuation subring of $M_0.\mathrm{placeOfPoint}\,x_0$.
--
--   This identifies the geometric generic fibre and the rational generic fibre of the Igusa model of $X_0(N)$ over $\mathbb{Z}_{(\ell)}$ with the two-chart models built from the integral closures of $k[j]$ and $k[j^{-1}]$ ($k = \bar{\mathbb{Q}}$, resp. $\mathbb{Q}$), pinning both isomorphisms chartwise and recording how Galois acts on places and how places of $\bar F_0$ restrict to places of $F_0$. It packages the $\bar{\mathbb{Q}}$-level identification together with its $\mathbb{Q}$-level twin and the place-compatibility clause required downstream, and is used by the statements producing the finite map data and the smooth proper model over $\mathbb{Q}$, and by the construction of the de Rham model package.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_exists_genericFibreIso_chartPin_galoisCompat_and_ratPlaceCompat.lean

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_ModularCurve_FibreModel
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_AlgebraicCurve_CurveModelConstruction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ModularCurve ModularCurve.CharPModel ModularCurve.IgusaScheme AlgebraicCurve
open scoped TensorProduct

noncomputable section
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.IgusaScheme.exists_genericFibreIso_chartPin_galoisCompat_and_ratPlaceCompat
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
            (b : ↥(modularFunctionFieldFull N)).2⟩ : modularFunctionFieldBar N))

    (htrans₀ : Transcendental ℚ (jFull N))
    [hne₀ : Fact (jFull N ≠ 0)]
    [hfd₀ : FiniteDimensional
      ↥(IntermediateField.adjoin ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N)))
      ↥(modularFunctionFieldFull N)]
    [hfd_inv₀ : FiniteDimensional
      ↥(IntermediateField.adjoin ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N)))
      ↥(modularFunctionFieldFull N)]
    (eFin₀ : ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgFin N ℓ) ≃ₐ[ℚ]
      ↥(AlgebraicCurve.CurveModel.chartRing ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N))))
    (hFin₀ : ∀ b : chartAlgFin N ℓ,
      ((eFin₀ (1 ⊗ₜ b) :
        ↥(AlgebraicCurve.CurveModel.chartRing ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N)))) :
          ↥(modularFunctionFieldFull N)) = (b : ↥(modularFunctionFieldFull N)))
    (eInf₀ : ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgInf N ℓ) ≃ₐ[ℚ]
      ↥(AlgebraicCurve.CurveModel.chartRing ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N))))
    (hInf₀ : ∀ b : chartAlgInf N ℓ,
      ((eInf₀ (1 ⊗ₜ b) :
        ↥(AlgebraicCurve.CurveModel.chartRing ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N)))) :
          ↥(modularFunctionFieldFull N)) = (b : ↥(modularFunctionFieldFull N))) :
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
      (∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (x x' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
        x'.1 ≫ eη ≫ pullback.fst (igusaTo N ℓ) _ =
          Spec.map (CommRingCat.ofHom (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
            x.1 ≫ eη ≫ pullback.fst (igusaTo N ℓ) _ →
        Mη.pointEquivPlace x' =
          arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) g •
            Mη.pointEquivPlace x) ∧
      let M₀ : CurveModel ℚ ↥(modularFunctionFieldFull N) :=
        CurveModel.ofGenerator ℚ (jFull N) htrans₀
      ∃ (e₀ : M₀.C ⟶ pullback (igusaTo N ℓ) (Spec.map (CommRingCat.ofHom
          (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ)))) (_ : IsIso e₀),
        e₀ ≫ pullback.snd (igusaTo N ℓ) _ = M₀.toBase ∧
        (AlgebraicCurve.CurveModel.ι₀ ℚ (jFull N) ≫ e₀ ≫ pullback.fst (igusaTo N ℓ) _ =
          Spec.map (CommRingCat.ofHom (eFin₀.toAlgHom.toRingHom.comp
            (Algebra.TensorProduct.includeRight
              (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := ℚ) (B := ↥(chartAlgFin N ℓ))).toRingHom)) ≫
            ModularCurve.IgusaScheme.ιFin N ℓ) ∧
        (AlgebraicCurve.CurveModel.ιInf ℚ (jFull N) ≫ e₀ ≫ pullback.fst (igusaTo N ℓ) _ =
          Spec.map (CommRingCat.ofHom (eInf₀.toAlgHom.toRingHom.comp
            (Algebra.TensorProduct.includeRight
              (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := ℚ) (B := ↥(chartAlgInf N ℓ))).toRingHom)) ≫
            ModularCurve.IgusaScheme.ιInf N ℓ) ∧
        ∀ (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
          (y : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶
            pullback (igusaTo N ℓ) (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ))))
          (x₀ : closedPoints M₀.C),
        y ≫ pullback.fst (igusaTo N ℓ) _ = x.1 ≫ eη ≫ pullback.fst (igusaTo N ℓ) _ →
        (y ≫ inv e₀).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) = x₀.1 →
        ((Mη.pointEquivPlace x).toValuationSubring.toSubring.comap
            ((baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull N)).toAlgHom.toRingHom.comp
              (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ)
                (B := ↥(modularFunctionFieldFull N))).toRingHom) =
          (M₀.placeOfPoint x₀).toValuationSubring.toSubring) := by sorry
