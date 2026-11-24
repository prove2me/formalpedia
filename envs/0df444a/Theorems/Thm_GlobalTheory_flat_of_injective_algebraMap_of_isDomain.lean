-- Prove2me | Theorems.Thm_GlobalTheory_flat_of_injective_algebraMap_of_isDomain
-- name    : GlobalTheory.flat_of_injective_algebraMap_of_isDomain
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:52:07.907855+00:00
-- url     : https://prove2.me/theorems/46a9ae39-6266-4c57-a7de-23b88fbbd322
-- title:
--   Global Theory: flat of injective algebra Map of is Domain
-- statement:
--   The Global Theory construction uses the flat of injective algebra Map of is Domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsIsMaximalTensorProductOfIsLocalHom.lean#L7-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsIsMaximalTensorProductOfIsLocalHom.lean#L7-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsIsMaximalTensorProductOfIsLocalHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory

theorem GlobalTheory.flat_of_injective_algebraMap_of_isDomain (O A : Type*) [CommRing O] [IsDomain O]
    [IsPrincipalIdealRing O] [CommRing A] [IsDomain A] [Algebra O A]
    (h : Function.Injective (algebraMap O A)) : Module.Flat O A := by sorry
