-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_ordAt_inv
-- name    : GroundTheory.ProfCoh.ordAt_inv
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:51:02.505147+00:00
-- url     : https://prove2.me/theorems/63ebe609-b902-46ed-98ea-18c887766542
-- title:
--   Prof Coh: ord At inv
-- statement:
--   The Prof Coh construction uses the ord At inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/SPicDefs.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/SPicDefs.lean#L20-L21

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_SPicDefs
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
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {F : Type*} [Field F] [NumberField F]

theorem GroundTheory.ProfCoh.ordAt_inv (v : HeightOneSpectrum (𝓞 F)) (x : Fˣ) : ordAt v x⁻¹ = -ordAt v x := by sorry
