-- Prove2me | Theorems.Thm_GlobalTheory_JR_Step_isClosed_unitaryGroup
-- name    : GlobalTheory.JR.Step.isClosed_unitaryGroup
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:38:19.23995+00:00
-- url     : https://prove2.me/theorems/7a712114-311c-4668-91bf-94dd88813de1
-- title:
--   Step: is Closed unitary Group
-- statement:
--   The Step construction uses the is Closed unitary Group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsClosedEmbeddingDiagOneUnitaryGroupEmbedding.lean#L25-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsClosedEmbeddingDiagOneUnitaryGroupEmbedding.lean#L25-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsClosedEmbeddingDiagOneUnitaryGroupEmbedding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Step

theorem GlobalTheory.JR.Step.isClosed_unitaryGroup (r : ℕ) (E : Type) [NormedField E] [StarRing E] [ContinuousStar E] :
    IsClosed (Matrix.unitaryGroup (Fin r) E : Set (Matrix (Fin r) (Fin r) E)) := by sorry
