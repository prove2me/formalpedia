-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_finite_setOf_ramified
-- name    : GroundTheory.ProfCoh.finite_setOf_ramified
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:02:31.460723+00:00
-- url     : https://prove2.me/theorems/44eaf375-9e3b-4a06-8cc1-34a9646613ef
-- title:
--   Prof Coh: finite set Of ramified
-- statement:
--   The Prof Coh construction uses the finite set Of ramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GlobalClassFormation/IdeleCohomology/Ramified.lean#L32-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GlobalClassFormation/IdeleCohomology/Ramified.lean#L32-L35

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalClassFormation_IdeleCohomology_Ramified
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
open IsDedekindDomain NumberField
variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]
variable (K L)

theorem GroundTheory.ProfCoh.finite_setOf_ramified :
    {w : HeightOneSpectrum (𝓞 L) | w.asIdeal.ramificationIdx (𝓞 K) ≠ 1}.Finite := by sorry
