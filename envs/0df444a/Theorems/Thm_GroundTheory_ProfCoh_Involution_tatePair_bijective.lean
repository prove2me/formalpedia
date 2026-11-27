-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_Involution_tatePair_bijective
-- name    : GroundTheory.ProfCoh.Involution.tatePair_bijective
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:01:52.737292+00:00
-- url     : https://prove2.me/theorems/6150e1ca-a175-494b-aec5-809282ca5a71
-- title:
--   Involution: tate Pair bijective
-- statement:
--   The Involution construction uses the tate Pair bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RealPlaces/InvolutionDuality.lean#L146-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RealPlaces/InvolutionDuality.lean#L146-L152

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

theorem GroundTheory.ProfCoh.Involution.tatePair_bijective [Finite M] : Function.Bijective (tatePair σ) := by sorry
