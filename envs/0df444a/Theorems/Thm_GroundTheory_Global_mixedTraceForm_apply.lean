-- Prove2me | Theorems.Thm_GroundTheory_Global_mixedTraceForm_apply
-- name    : GroundTheory.Global.mixedTraceForm_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:57:38.120203+00:00
-- url     : https://prove2.me/theorems/6a1cd423-be7d-460e-bbcb-4011e9ab161c
-- title:
--   Global: mixed Trace Form apply
-- statement:
--   The Global construction uses the mixed Trace Form apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TracePairing.lean#L60-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TracePairing.lean#L60-L61

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

theorem GroundTheory.Global.mixedTraceForm_apply (x y : mixedSpace K) :
    mixedTraceForm K x y = mixedTrace K (x * y) := by sorry
