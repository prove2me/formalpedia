-- Prove2me | Theorems.Thm_GlobalTheory_T_weilRepresentationExistsEtale_of_subsingleton
-- name    : GlobalTheory.T.weilRepresentationExistsEtale_of_subsingleton
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:01:12.826289+00:00
-- url     : https://prove2.me/theorems/d88b06e8-d245-493e-b1f8-7242824d3751
-- title:
--   T: weil Representation Exists Etale of subsingleton
-- statement:
--   The T construction uses the weil Representation Exists Etale of subsingleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WeilRepresentationExistsEtaleOfSubsingletonStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WeilRepresentationExistsEtaleOfSubsingletonStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilRepresentationExistsEtaleOfSubsingleton
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSplitting
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilRepresentationExistsEtaleOfSubsingletonStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.weilRepresentationExistsEtale_of_subsingleton : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), Subsingleton A.K → WeilAt A := by sorry
