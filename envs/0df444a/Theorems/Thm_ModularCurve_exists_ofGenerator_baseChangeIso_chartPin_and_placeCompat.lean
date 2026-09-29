-- Prove2me | Theorems.Thm_ModularCurve_exists_ofGenerator_baseChangeIso_chartPin_and_placeCompat
-- name    : ModularCurve.exists_ofGenerator_baseChangeIso_chartPin_and_placeCompat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/91535f04-6a16-55fb-91eb-3c2f5d7a00ec
-- title:
--   Base change of the two-chart model to ℚ̄
-- statement:
--   Let $N$ be a nonzero natural number, write $F =$ `modularFunctionFieldFull N` for the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the divisor expansions at level $N$, and $\bar F =$ `modularFunctionFieldBar N` for its coefficientwise base change inside $\overline{\mathbb{Q}}((q))$; let $j =$ `jFull N` $\in F$ and $\bar j =$ `jBar N` $\in \bar F$ be the $q$-expansions of the $j$-invariant. Assume $\bar j$ is transcendental over $\overline{\mathbb{Q}}$ and nonzero, with $\bar F$ finite over $\overline{\mathbb{Q}}(\bar j)$ and over $\overline{\mathbb{Q}}(\bar j^{-1})$, and likewise $j$ transcendental over $\mathbb{Q}$ and nonzero with $F$ finite over $\mathbb{Q}(j)$ and over $\mathbb{Q}(j^{-1})$. For $S \in \{\{j\},\{j^{-1}\}\}$ the chart ring `chartRing` is the subalgebra of elements integral over $\mathbb{Q}[S]$, and similarly over $\overline{\mathbb{Q}}$; assume given $\overline{\mathbb{Q}}$-algebra isomorphisms $c_{\mathrm{fin}} : \overline{\mathbb{Q}} \otimes_{\mathbb{Q}} A_{\{j\}} \to \bar A_{\{\bar j\}}$ and $c_{\infty} : \overline{\mathbb{Q}} \otimes_{\mathbb{Q}} A_{\{j^{-1}\}} \to \bar A_{\{\bar j^{-1}\}}$, each sending $1 \otimes b$ to the element of $\bar F$ obtained by applying `coeffEmb` (coefficientwise extension along $\mathbb{Q} \to \overline{\mathbb{Q}}$) to $b$. Let $M_\eta =$ `CurveModel.ofGenerator` $\overline{\mathbb{Q}}\,\bar j$ and $M_0 =$ `CurveModel.ofGenerator` $\mathbb{Q}\,j$ be the resulting two-chart smooth proper models, glued from the spectra of the chart rings. Then there exists a morphism $e_\eta : M_\eta.C \to M_0.C \times_{\operatorname{Spec}\mathbb{Q}} \operatorname{Spec}\overline{\mathbb{Q}}$, together with the assertion that it is an isomorphism, such that: $e_\eta$ followed by the second projection is $M_\eta$'s structure morphism to $\operatorname{Spec}\overline{\mathbb{Q}}$; for every section $y$ of $M_\eta.toBase$ and every closed point $y_0$ of $M_0.C$ such that $y$ followed by $e_\eta$ and the first projection carries the closed point of $\operatorname{Spec}\overline{\mathbb{Q}}$ to $y_0$, the valuation subring of the place `Mη.pointEquivPlace y` of $\bar F/\overline{\mathbb{Q}}$, contracted along $F \to \overline{\mathbb{Q}} \otimes_{\mathbb{Q}} F \xrightarrow{\sim} \bar F$ (the right inclusion followed by `baseChangeEquiv`), equals the valuation subring of `M₀.placeOfPoint y₀` as a subring of $F$; and, on each chart, the chart immersion $\iota_0$ (resp. $\iota_\infty$) of $M_\eta$ followed by $e_\eta$ and the first projection equals $\operatorname{Spec}$ of $A_S \to \overline{\mathbb{Q}} \otimes_{\mathbb{Q}} A_S \xrightarrow{c} \bar A_S$ followed by the corresponding chart immersion of $M_0$.
--
--   This identifies the two-chart model of the level-$N$ modular function field over $\overline{\mathbb{Q}}$ with the base change to $\overline{\mathbb{Q}}$ of the model over $\mathbb{Q}$, in a form pinned down on both charts and compatible with the bijections between closed points and places. It is used in the construction over $\mathbb{Q}$ of Hecke endomorphisms of the relative Jacobian and of the associated morphisms of models, where the geometric model and its places must be recognised as the base change of the rational one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_ofGenerator_baseChangeIso_chartPin_and_placeCompat.lean

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

theorem ModularCurve.exists_ofGenerator_baseChangeIso_chartPin_and_placeCompat
    (N : ℕ) [NeZero N]

    (htrans : Transcendental (AlgebraicClosure ℚ) (jBar N))
    [hne : Fact (jBar N ≠ 0)]
    [hfd : FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({jBar N} : Set (modularFunctionFieldBar N))) (modularFunctionFieldBar N)]
    [hfd_inv : FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({(jBar N)⁻¹} : Set (modularFunctionFieldBar N))) (modularFunctionFieldBar N)]

    (htrans₀ : Transcendental ℚ (jFull N))
    [hne₀ : Fact (jFull N ≠ 0)]
    [hfd₀ : FiniteDimensional
      ↥(IntermediateField.adjoin ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N))) ↥(modularFunctionFieldFull N)]
    [hfd_inv₀ : FiniteDimensional
      ↥(IntermediateField.adjoin ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N))) ↥(modularFunctionFieldFull N)]

    (cFin : (AlgebraicClosure ℚ) ⊗[ℚ] ↥(AlgebraicCurve.CurveModel.chartRing ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N))) ≃ₐ[AlgebraicClosure ℚ]
      ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({jBar N} : Set (modularFunctionFieldBar N))))
    (hcFin : ∀ b : AlgebraicCurve.CurveModel.chartRing ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N)),
      ((cFin (1 ⊗ₜ b) : ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({jBar N} : Set (modularFunctionFieldBar N)))) : (modularFunctionFieldBar N)) =
        (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b : ↥(modularFunctionFieldFull N)).2⟩ : (modularFunctionFieldBar N)))
    (cInf : (AlgebraicClosure ℚ) ⊗[ℚ] ↥(AlgebraicCurve.CurveModel.chartRing ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N))) ≃ₐ[AlgebraicClosure ℚ]
      ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({(jBar N)⁻¹} : Set (modularFunctionFieldBar N))))
    (hcInf : ∀ b : AlgebraicCurve.CurveModel.chartRing ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N)),
      ((cInf (1 ⊗ₜ b) : ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({(jBar N)⁻¹} : Set (modularFunctionFieldBar N)))) : (modularFunctionFieldBar N)) =
        (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b : ↥(modularFunctionFieldFull N)).2⟩ : (modularFunctionFieldBar N))) :
    let Mη : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := CurveModel.ofGenerator (AlgebraicClosure ℚ) (jBar N) htrans
    let M₀ : CurveModel ℚ ↥(modularFunctionFieldFull N) := CurveModel.ofGenerator ℚ (jFull N) htrans₀
    ∃ (eη : Mη.C ⟶ pullback M₀.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))))
      (_ : IsIso eη),
      eη ≫ pullback.snd _ _ = Mη.toBase ∧
      (∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
        (y₀ : closedPoints M₀.C),
      (y.1 ≫ eη ≫ pullback.fst _ _).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) = y₀.1 →
      ((Mη.pointEquivPlace y).toValuationSubring.toSubring.comap
          ((baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull N)).toAlgHom.toRingHom.comp
            (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ) (B := ↥(modularFunctionFieldFull N))).toRingHom) =
        (M₀.placeOfPoint y₀).toValuationSubring.toSubring)) ∧
      (AlgebraicCurve.CurveModel.ι₀ (AlgebraicClosure ℚ) (jBar N) ≫ eη ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (cFin.toAlgHom.toRingHom.comp
          (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ)
            (B := ↥(AlgebraicCurve.CurveModel.chartRing ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N))))).toRingHom)) ≫
          AlgebraicCurve.CurveModel.ι₀ ℚ (jFull N)) ∧
      (AlgebraicCurve.CurveModel.ιInf (AlgebraicClosure ℚ) (jBar N) ≫ eη ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (cInf.toAlgHom.toRingHom.comp
          (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ)
            (B := ↥(AlgebraicCurve.CurveModel.chartRing ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N))))).toRingHom)) ≫
          AlgebraicCurve.CurveModel.ιInf ℚ (jFull N)) := by sorry
