-- Prove2me | Theorems.Thm_GroundTheory_Global_dualSubmodule_idealLattice
-- name    : GroundTheory.Global.dualSubmodule_idealLattice
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:40:30.9629+00:00
-- url     : https://prove2.me/theorems/d0dd7c89-e816-4bbf-a4d0-7a54e1a0c342
-- title:
--   Global: dual Submodule ideal Lattice
-- statement:
--   The Global construction uses the dual Submodule ideal Lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TraceDualLattice.lean#L33-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TraceDualLattice.lean#L33-L57

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

theorem GroundTheory.Global.dualSubmodule_idealLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (mixedTraceForm K).dualSubmodule (idealLattice K I) = idealLattice K (traceDualIdeal K I) := by sorry
