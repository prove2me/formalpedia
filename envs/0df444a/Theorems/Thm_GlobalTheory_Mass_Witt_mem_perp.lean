-- Prove2me | Theorems.Thm_GlobalTheory_Mass_Witt_mem_perp
-- name    : GlobalTheory.Mass.Witt.mem_perp
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:53:30.738182+00:00
-- url     : https://prove2.me/theorems/7771a85d-28e8-40d9-86cf-ceb492b2c004
-- title:
--   Witt: mem perp
-- statement:
--   The Witt construction uses the mem perp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittExtensionTotallyDefiniteHermitian.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittExtensionTotallyDefiniteHermitian.lean#L11-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionTotallyDefiniteHermitian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.Witt
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

theorem GlobalTheory.Mass.Witt.mem_perp (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) (v : V) :
    v ∈ perp h U ↔ ∀ x ∈ U, h x v = 0 := by sorry
