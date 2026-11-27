-- Prove2me | Theorems.Thm_GlobalTheory_isReduced_genericFibre_of_isReduced
-- name    : GlobalTheory.isReduced_genericFibre_of_isReduced
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:48:53.455024+00:00
-- url     : https://prove2.me/theorems/cf89702b-bbee-4120-be0e-2aecc8f1ab4a
-- title:
--   Global Theory: is Reduced generic Fibre of is Reduced
-- statement:
--   The Global Theory construction uses the is Reduced generic Fibre of is Reduced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/IsReducedGenericFibreOfIsReduced.lean#L7-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/IsReducedGenericFibreOfIsReduced.lean#L7-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsReducedGenericFibreOfIsReduced
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory

theorem GlobalTheory.isReduced_genericFibre_of_isReduced :
    ∀ (O C Q : Type) [CommRing O] [IsDomain O] [Field C] [Algebra O C] [IsFractionRing O C]
      [CommRing Q] [Algebra O Q], IsReduced Q → IsReduced (C ⊗[O] Q) := by sorry
