-- Prove2me | Theorems.Thm_GroundTheory_Global_mixedTraceForm_comm
-- name    : GroundTheory.Global.mixedTraceForm_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:55.416257+00:00
-- url     : https://prove2.me/theorems/4bfbc286-877d-45ae-832c-f21a201e766f
-- title:
--   Global: mixed Trace Form comm
-- statement:
--   The Global construction uses the mixed Trace Form comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TracePairing.lean#L66-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TracePairing.lean#L66-L68

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_IntegersLattice
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TracePairing
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
open scoped Classical ComplexConjugate RealInnerProductSpace FourierTransform Real
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem GroundTheory.Global.mixedTraceForm_comm (x y : mixedSpace K) :
    mixedTraceForm K x y = mixedTraceForm K y x := by sorry
