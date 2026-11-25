-- Prove2me | Theorems.Thm_GroundTheory_Global_mixedTrace_mixedEmbedding
-- name    : GroundTheory.Global.mixedTrace_mixedEmbedding
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:42:06.233123+00:00
-- url     : https://prove2.me/theorems/7f96367f-19e7-47bc-8025-8f673672b29a
-- title:
--   Global: mixed Trace mixed Embedding
-- statement:
--   The Global construction uses the mixed Trace mixed Embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TracePairing.lean#L28-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TracePairing.lean#L28-L55

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

theorem GroundTheory.Global.mixedTrace_mixedEmbedding (x : K) :
    mixedTrace K (mixedEmbedding K x) = (Algebra.trace ℚ K x : ℝ) := by sorry
