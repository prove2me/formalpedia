-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_smulPlace_asIdeal
-- name    : GroundTheory.ProfCoh.smulPlace_asIdeal
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:50:42.457617+00:00
-- url     : https://prove2.me/theorems/eacbd790-842d-472f-a9d2-bb01a51f7fe0
-- title:
--   Prof Coh: smul Place as Ideal
-- statement:
--   The Prof Coh construction uses the smul Place as Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/ValuationTransport.lean#L39-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/ValuationTransport.lean#L39-L41

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_ValuationTransport
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
open scoped Pointwise
variable {B : Type*} [CommRing B] [IsDedekindDomain B] {G : Type*} [Group G]
  [MulSemiringAction G B]
omit [IsDedekindDomain B]

theorem GroundTheory.ProfCoh.smulPlace_asIdeal (σ : G) (w : HeightOneSpectrum B) :
    (smulPlace σ w).asIdeal = σ • w.asIdeal := by sorry
