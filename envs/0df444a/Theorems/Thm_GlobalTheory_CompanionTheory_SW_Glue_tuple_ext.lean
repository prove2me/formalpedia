-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Glue_tuple_ext
-- name    : GlobalTheory.CompanionTheory.SW.Glue.tuple_ext
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:05:35.699868+00:00
-- url     : https://prove2.me/theorems/64d21707-d1e3-4e0a-a5df-b9199ed34825
-- title:
--   Glue: tuple ext
-- statement:
--   The Glue construction uses the tuple ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicTupleLocalGlobalProperties.lean#L84-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicTupleLocalGlobalProperties.lean#L84-L95

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
include b

theorem GlobalTheory.CompanionTheory.SW.Glue.tuple_ext (X Y : Fin n → Fin M → AF F ⊗[F] E) (hinf : projInf X = projInf Y)
    (hv : ∀ v, projV v (projFin X) = projV v (projFin Y)) : X = Y := by sorry
