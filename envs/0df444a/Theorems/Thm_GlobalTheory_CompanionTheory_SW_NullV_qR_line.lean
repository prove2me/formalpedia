-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_NullV_qR_line
-- name    : GlobalTheory.CompanionTheory.SW.NullV.qR_line
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:20:50.314908+00:00
-- url     : https://prove2.me/theorems/51d720d5-82ce-4448-8e1c-c7be06e38ebf
-- title:
--   Null V: q R line
-- statement:
--   The Null V construction uses the q R line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HaarMeasureNonunitsNull.lean#L100-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HaarMeasureNonunitsNull.lean#L100-L121

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianNondegRepresentsNonzeroScalar
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CompletionIsLocalRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HaarMeasureNonunitsNull
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
open scoped Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.NullV
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem GlobalTheory.CompanionTheory.SW.NullV.qR_line [Module.Free F E] [Module.Finite F E] (x y : Fin M → R ⊗[F] E) (s : R) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J (fun j => x j + algebraMap R (R ⊗[F] E) s * y j) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J x +
        s * (algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E)
          (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J x y + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J y x)) +
        s ^ 2 * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J y := by sorry
