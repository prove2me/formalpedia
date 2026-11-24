-- Prove2me | Theorems.Thm_GlobalTheory_isAdicComplete_map_of_finite
-- name    : GlobalTheory.isAdicComplete_map_of_finite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:07:01.504211+00:00
-- url     : https://prove2.me/theorems/7dc794f1-478d-46eb-85d4-7d087372c7a9
-- title:
--   Global Theory: is Adic Complete map of finite
-- statement:
--   The Global Theory construction uses the is Adic Complete map of finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueAlgEquivOfCompatibleQuotient.lean#L33-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueAlgEquivOfCompatibleQuotient.lean#L33-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open TensorProduct

theorem GlobalTheory.isAdicComplete_map_of_finite {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    [IsAdicComplete I R] (S : Type*) [CommRing S] [Algebra R S] [Module.Finite R S] :
    IsAdicComplete (I.map (algebraMap R S)) S := by sorry
