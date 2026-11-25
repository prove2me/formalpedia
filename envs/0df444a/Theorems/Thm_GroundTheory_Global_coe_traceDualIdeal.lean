-- Prove2me | Theorems.Thm_GroundTheory_Global_coe_traceDualIdeal
-- name    : GroundTheory.Global.coe_traceDualIdeal
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:40:19.670671+00:00
-- url     : https://prove2.me/theorems/d183597a-75d6-4d84-ace3-21c9abd70ba2
-- title:
--   Global: coe trace Dual Ideal
-- statement:
--   The Global construction uses the coe trace Dual Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TraceDualLattice.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TraceDualLattice.lean#L17-L19

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceFourier
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceDualLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module MeasureTheory
open scoped Classical ENNReal nonZeroDivisors
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem GroundTheory.Global.coe_traceDualIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (traceDualIdeal K I : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) := by sorry
