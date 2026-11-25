-- Prove2me | Theorems.Thm_GlobalTheory_DictPinCompare_typings_compare
-- name    : GlobalTheory.DictPinCompare.typings_compare
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:04:38.299812+00:00
-- url     : https://prove2.me/theorems/506c87be-73d4-54cb-82c9-7b8f6325cb29
-- title:
--   Dict Pin Compare: typings compare
-- statement:
--   The Dict Pin Compare construction uses the typings compare property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/OrthogonalFrameIff.lean#L799-L851
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/OrthogonalFrameIff.lean#L799-L851

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LatticeEmbeddingHalf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CramerMemAdelicCompletionOfElementSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_InfAdeleTensorBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_OrthogonalFrameIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.DictPinCompare
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase (Fin𝔸 Inf𝔸 toFin latAd latBase CongrAt half IsLatEmb crd vec IsModelOf IsOrthoFrame IsArchAt
  IsRatUnitary ratTo LatMark IsMarkStab IsLevelStab IsDictOf IsFamilyOf unitaryOver AdelicU AdPinU)
open scoped TensorProduct nonZeroDivisors Matrix
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra F E]
  {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W] {n r : ℕ}
  (fr : Module.Basis (Fin n) E W) (hT : W →ₛₗ[conjHom E] W →ₗ[E] E) (L0 : Submodule (𝓞 E) W)
  (AA : FractionalIdeal (𝓞 E)⁰ E) (xi0 : E) {G : Type} [Group G]
  (infHom : G →* GL (Fin n) (Inf𝔸 F ⊗[F] E)) (finHom : G →* GL (Fin n) (Fin𝔸 F ⊗[F] E)) (GQ GfC : Subgroup G)
variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ}

theorem GlobalTheory.DictPinCompare.typings_compare [IsTotallyReal F] (cj : E ≃ₐ[F] E) (hcj : ∀ x, cj x = cc x)
    (hF : ∀ x : E, cc x = x → x ∈ Set.range (algebraMap F E))
    (hfg : L0.FG) (hsp : Submodule.span E (L0 : Set W) = ⊤) (hA : AA ≠ 0)
    (hherm : ∀ x y, cc (hT x y) = hT y x) (hnd : (gramOf fr hT).det ≠ 0) (hxi : cc xi0 = -xi0)
    (hsgn : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → 0 < (τ xi0).im) (U : Unf Xo c σ r) (hr : n = r)
    (dict : AdelicU F cj fr (flipForm hT) → Σ k, Frame (U.X k).Ψ r) (Kf : Subgroup (AdelicU F cj fr (flipForm hT))) :
    let h := flipForm hT
    let 𝔄 : Submodule (𝓞 E) E := AA
    let inf := infU fr cj h
    let fin := finU fr cj h

    (∀ v, finVec F (coord fr v) = toFin F fr v) ∧
    (∀ g, latGHat F fr L0 AA fin g = latAd F fr L0 𝔄 (fin g)) ∧
    (∀ g, latG F fr L0 AA fin g = (GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latG F fr L0 𝔄 (fin g)).map (coord fr).toLinearMap) ∧

    (∀ ι : Dw.La →ₗ[𝓞 E] W, (LatEmb F fr L0 AA fin ((coord fr).toLinearMap ∘ₗ ι) ∧
      LatIsom fr hT xi0 Dw.EF ((coord fr).toLinearMap ∘ₗ ι)) ↔ IsLatEmb h L0 𝔄 xi0 Dw ι) ∧
    (∀ X : Data E r, (ModelW fr hT xi0 hr X ∧ TypeClause H Dw.q X) ↔ IsModelOf H hr fr h xi0 Dw.q X) ∧
    (∀ (X : Data E r) x₀, IsOrthogonalFrame X x₀ ↔ IsOrthoFrame X x₀) ∧
    (∀ ι : Dw.La →ₗ[𝓞 E] W, LinearMap.range ι = latBase L0 𝔄 →
      (KfHalf F fr L0 fin inf.ker Kf l.M (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ↔ IsLevelStab F fr L0 𝔄 l ι inf fin Kf)) ∧

    (∀ (ι : Dw.La →ₗ[𝓞 E] W) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
      (Fm : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
      (ik : U.Comp → Fin Fm.n) (φ : ∀ k, (Fm.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ)
      (th : (E →+* ℂ) → (Inf𝔸 F ⊗[F] E →+* ℂ)) (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ),
      DictLat F fr L0 AA inf fin (ratU fr cj h) U hr dict ((coord fr).toLinearMap ∘ₗ ι) e Fm ik φ
          (fun _ τ => th τ.1) x₀ ↔
        IsFamilyOf U e Fm ik φ ∧
          IsDictOf F hr fr h L0 𝔄 l ι U.X (fun k a => φ k (Fm.t (ik k) a)) th x₀ inf fin dict) ∧

    (AdPinU F cj hr fr h L0 𝔄 xi0 U dict Kf ↔ ∃ x₀ ι₀, SidePins fr hT L0 xi0 fin inf.ker U hr Kf x₀ ∧
      AdPinWith F fr hT L0 AA xi0 inf fin (ratU fr cj h) U dict x₀ ι₀ fun k mk => IsMarkStab l (U.X k) mk ∧
        ∃ gk, LatMark F hr fr L0 𝔄 l (embW fr hr ι₀) (U.X k) mk (fin gk)) ∧
    (AdPinU F cj hr fr h L0 𝔄 xi0 U dict Kf → ∃ x₀ ι₀, SidePins fr hT L0 xi0 fin inf.ker U hr Kf x₀ ∧
      AdPin F fr hT L0 AA xi0 inf fin (ratU fr cj h) U dict x₀ ι₀) ∧
    ((∀ k, ∃ g, (dict g).1 = k) →
      (AdPinU F cj hr fr h L0 𝔄 xi0 U dict Kf ↔ ∃ x₀ ι₀, SidePins fr hT L0 xi0 fin inf.ker U hr Kf x₀ ∧
        AdPinWith F fr hT L0 AA xi0 inf fin (ratU fr cj h) U dict x₀ ι₀ fun k mk => IsMarkStab l (U.X k) mk)) := by sorry
