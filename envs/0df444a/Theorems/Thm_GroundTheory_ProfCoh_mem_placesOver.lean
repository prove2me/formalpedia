-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_mem_placesOver
-- name    : GroundTheory.ProfCoh.mem_placesOver
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:02:16.613586+00:00
-- url     : https://prove2.me/theorems/24235b12-b7ba-47c0-9a6c-6c709fc3c3d4
-- title:
--   Prof Coh: mem places Over
-- statement:
--   The Prof Coh construction uses the mem places Over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/MaxUnramifiedOutside.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/MaxUnramifiedOutside.lean#L16-L18

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_MaxUnramifiedOutside
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.ProfCoh
open NumberField IsDedekindDomain
variable {F : Type*} [Field F]
variable {L : Type*} [Field L] [Algebra F L]

theorem GroundTheory.ProfCoh.mem_placesOver {S : Set (HeightOneSpectrum (𝓞 F))} {w : HeightOneSpectrum (𝓞 L)} :
    w ∈ placesOver S ↔ ∃ v ∈ S, w.asIdeal.LiesOver v.asIdeal := by sorry
