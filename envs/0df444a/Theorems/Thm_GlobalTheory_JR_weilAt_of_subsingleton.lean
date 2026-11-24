-- Prove2me | Theorems.Thm_GlobalTheory_JR_weilAt_of_subsingleton
-- name    : GlobalTheory.JR.weilAt_of_subsingleton
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:40:10.812817+00:00
-- url     : https://prove2.me/theorems/fc1bc73f-1ea6-48b8-8fb8-db30733c6ddf
-- title:
--   JR: weil At of subsingleton
-- statement:
--   The JR construction uses the weil At of subsingleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WeilRepresentationExistsEtaleOfSubsingleton.lean#L8-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WeilRepresentationExistsEtaleOfSubsingleton.lean#L8-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSplitting
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilRepresentationExistsEtaleOfSubsingleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR

theorem GlobalTheory.JR.weilAt_of_subsingleton (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (hK : Subsingleton A.K) : WeilAt A := by sorry
