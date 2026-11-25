-- Prove2me | Theorems.Thm_GlobalTheory_MassOrth_mem_biInt
-- name    : GlobalTheory.MassOrth.mem_biInt
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:14:22.835587+00:00
-- url     : https://prove2.me/theorems/9bae54d3-a688-4405-8a11-e2065e6f3ac8
-- title:
--   Mass Orth: mem bi Int
-- statement:
--   The Mass Orth construction uses the mem bi Int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsMaxVector.lean#L29-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsMaxVector.lean#L29-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMaxVector
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
open GlobalTheory GlobalTheory.MassOrth
variable {K V Γ : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)

theorem GlobalTheory.MassOrth.mem_biInt {k : K} : k ∈ biInt v ↔ v k ≤ 1 ∧ v (star k) ≤ 1 := by sorry
