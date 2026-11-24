-- Prove2me | Theorems.Thm_GlobalTheory_DictPinCompare_latAd_eq_of_stab
-- name    : GlobalTheory.DictPinCompare.latAd_eq_of_stab
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:18:53.208805+00:00
-- url     : https://prove2.me/theorems/cce4a005-b667-4af3-85c1-dc84e69fe521
-- title:
--   Dict Pin Compare: lat Ad eq of stab
-- statement:
--   The Dict Pin Compare construction uses the lat Ad eq of stab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/OrthogonalFrameIff.lean#L380-L389
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/OrthogonalFrameIff.lean#L380-L389

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
omit [IsCMField E]

theorem GlobalTheory.DictPinCompare.latAd_eq_of_stab {k : GL (Fin n) (Fin𝔸 F ⊗[F] E)}
    (h1 : ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0, k.1 *ᵥ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0)
    (h2 : ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0, k⁻¹.1 *ᵥ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0) :
    latAd F fr L0 (AA : Submodule (𝓞 E) E) k = latAd F fr L0 (AA : Submodule (𝓞 E) E) 1 := by sorry
