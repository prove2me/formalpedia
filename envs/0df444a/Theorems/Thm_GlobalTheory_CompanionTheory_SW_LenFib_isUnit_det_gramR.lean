-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_LenFib_isUnit_det_gramR
-- name    : GlobalTheory.CompanionTheory.SW.LenFib.isUnit_det_gramR
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:06:41.675328+00:00
-- url     : https://prove2.me/theorems/639c20be-8c82-4996-a1bb-4ffbb5f7699d
-- title:
--   Len Fib: is Unit det gram R
-- statement:
--   The Len Fib construction uses the is Unit det gram R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IsFibreFamilyLength.lean#L74-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IsFibreFamilyLength.lean#L74-L79

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ContinuousHermScal
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsFibreFamilyLength
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LenFib
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R]

theorem GlobalTheory.CompanionTheory.SW.LenFib.isUnit_det_gramR [TopologicalSpace R] [IsTopologicalRing R] {σ : E →ₐ[F] E}
    (hσ : IsCMExt F E σ) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) {X : Fin 1 → Fin M → R ⊗[F] E}
    (h : IsUnit (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J (X 0))) : IsUnit (gramR R σ J X).det := by sorry
