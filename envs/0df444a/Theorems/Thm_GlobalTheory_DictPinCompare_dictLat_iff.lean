-- Prove2me | Theorems.Thm_GlobalTheory_DictPinCompare_dictLat_iff
-- name    : GlobalTheory.DictPinCompare.dictLat_iff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T14:19:03.399808+00:00
-- url     : https://prove2.me/theorems/3269fb12-09ba-4825-961c-162cd589afe2
-- title:
--   Dict Pin Compare: dict Lat iff
-- statement:
--   The Dict Pin Compare construction uses the dict Lat iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/OrthogonalFrameIff.lean#L562-L584
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/OrthogonalFrameIff.lean#L562-L584

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

theorem GlobalTheory.DictPinCompare.dictLat_iff (hQ : IsRatPoints F fr hT infHom finHom GQ) (U : Unf Xo c σ r) (hr : n = r)
    (dict : G → Σ k, Frame (U.X k).Ψ r) (ι : Dw.La →ₗ[𝓞 E] W) {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (Fm : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin Fm.n) (φ : ∀ k, (Fm.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ)
    (th : (E →+* ℂ) → (Inf𝔸 F ⊗[F] E →+* ℂ)) (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) :
    DictLat F fr L0 AA infHom finHom GQ U hr dict ((coord fr).toLinearMap ∘ₗ ι) e Fm ik φ (fun _ τ => th τ.1) x₀ ↔
      IsFamilyOf U e Fm ik φ ∧ IsDictOf F hr fr (flipForm hT) L0 (AA : Submodule (𝓞 E) E) l ι U.X
        (fun k a => φ k (Fm.t (ik k) a)) th x₀ infHom finHom dict := by sorry
