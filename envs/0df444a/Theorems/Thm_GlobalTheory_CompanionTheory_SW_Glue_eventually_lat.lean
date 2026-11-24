-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Glue_eventually_lat
-- name    : GlobalTheory.CompanionTheory.SW.Glue.eventually_lat
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:05:29.061788+00:00
-- url     : https://prove2.me/theorems/58798a22-5af6-4675-8cbb-aa5de99b3fb8
-- title:
--   Glue: eventually lat
-- statement:
--   The Glue construction uses the eventually lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicTupleLocalGlobalProperties.lean#L97-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicTupleLocalGlobalProperties.lean#L97-L110

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicTupleLocalGlobalProperties
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix RestrictedProduct
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Glue
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
variable {d M n : ℕ} (b : Module.Basis (Fin d) F E)

theorem GlobalTheory.CompanionTheory.SW.Glue.eventually_lat (X : Fin n → Fin M → AF F ⊗[F] E) :
    ∀ᶠ v in Filter.cofinite, projV v (projFin X) ∈ latV b v := by sorry
