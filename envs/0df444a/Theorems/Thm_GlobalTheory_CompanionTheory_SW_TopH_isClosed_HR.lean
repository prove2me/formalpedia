-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_TopH_isClosed_HR
-- name    : GlobalTheory.CompanionTheory.SW.TopH.isClosed_HR
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:12:03.743314+00:00
-- url     : https://prove2.me/theorems/75eaf49f-2f06-4a4a-8d94-68481c4906a2
-- title:
--   Top H: is Closed HR
-- statement:
--   The Top H construction uses the is Closed HR property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicUnitaryGroupLocallyCompact.lean#L32-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicUnitaryGroupLocallyCompact.lean#L32-L40

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupLocallyCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.TopH
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]

theorem GlobalTheory.CompanionTheory.SW.TopH.isClosed_HR [IsTopologicalRing (R ⊗[F] E)] [T2Space (R ⊗[F] E)] (σ : E →ₐ[F] E) (hs : Continuous (sigR R σ)) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) :
    IsClosed (HR R σ J : Set (GL (Fin M) (R ⊗[F] E))) := by sorry
