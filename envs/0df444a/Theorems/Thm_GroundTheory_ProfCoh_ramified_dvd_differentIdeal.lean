-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_ramified_dvd_differentIdeal
-- name    : GroundTheory.ProfCoh.ramified_dvd_differentIdeal
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:50:57.786312+00:00
-- url     : https://prove2.me/theorems/7fece830-04a5-4015-8938-ebd8747991a6
-- title:
--   Prof Coh: ramified dvd different Ideal
-- statement:
--   The Prof Coh construction uses the ramified dvd different Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GlobalClassFormation/IdeleCohomology/Ramified.lean#L10-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GlobalClassFormation/IdeleCohomology/Ramified.lean#L10-L28

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

theorem GroundTheory.ProfCoh.ramified_dvd_differentIdeal {w : HeightOneSpectrum (𝓞 L)}
    (h : w.asIdeal.ramificationIdx (𝓞 K) ≠ 1) :
    w.asIdeal ∣ differentIdeal (𝓞 K) (𝓞 L) := by sorry
