-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_Involution_tatePair_injective
-- name    : GroundTheory.ProfCoh.Involution.tatePair_injective
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:10:48.816252+00:00
-- url     : https://prove2.me/theorems/ecb0e7c1-7a45-5265-9e81-0a7b787c3e13
-- title:
--   Involution: tate Pair injective
-- statement:
--   The Involution construction uses the tate Pair injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RealPlaces/InvolutionDuality.lean#L107-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RealPlaces/InvolutionDuality.lean#L107-L123

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
variable {σ : M →+ M}

theorem GroundTheory.ProfCoh.Involution.tatePair_injective : Function.Injective (tatePair σ) := by sorry
