-- Prove2me | Theorems.Thm_GroundTheory_Global_coeToSubmodule_traceDualIdeal
-- name    : GroundTheory.Global.coeToSubmodule_traceDualIdeal
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:40:20.24899+00:00
-- url     : https://prove2.me/theorems/adad7e22-76b7-48b5-a356-ac7006eee964
-- title:
--   Global: coe To Submodule trace Dual Ideal
-- statement:
--   The Global construction uses the coe To Submodule trace Dual Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TraceDualLattice.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TraceDualLattice.lean#L21-L24

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

theorem GroundTheory.Global.coeToSubmodule_traceDualIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ((traceDualIdeal K I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) =
      Submodule.traceDual ℤ ℚ (I : Submodule (𝓞 K) K) := by sorry
