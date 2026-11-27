-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_Involution_two_nsmul_fixedPair
-- name    : GroundTheory.ProfCoh.Involution.two_nsmul_fixedPair
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:02:14.68302+00:00
-- url     : https://prove2.me/theorems/0933b442-756c-4994-b1b7-364fc8abb457
-- title:
--   Involution: two nsmul fixed Pair
-- statement:
--   The Involution construction uses the two nsmul fixed Pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RealPlaces/InvolutionDuality.lean#L65-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RealPlaces/InvolutionDuality.lean#L65-L70

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_TorsionDualFinite
import Definitions.Def_GroundTheory_ProfiniteCohomology_RealPlaces_InvolutionDuality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open GroundTheory.ProfCoh.Involution
variable {M : Type*} [AddCommGroup M]

theorem GroundTheory.ProfCoh.Involution.two_nsmul_fixedPair (σ : M →+ M) (x : fixedSub σ) (f : fixedSub (dualInv σ)) :
    2 • fixedPair σ x f = 0 := by sorry
