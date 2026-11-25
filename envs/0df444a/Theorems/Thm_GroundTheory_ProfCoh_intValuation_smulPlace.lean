-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_intValuation_smulPlace
-- name    : GroundTheory.ProfCoh.intValuation_smulPlace
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:51:00.623065+00:00
-- url     : https://prove2.me/theorems/78a8de71-92db-4c64-9458-86da0b1c1ce2
-- title:
--   Prof Coh: int Valuation smul Place
-- statement:
--   The Prof Coh construction uses the int Valuation smul Place property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/ValuationTransport.lean#L43-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/ValuationTransport.lean#L43-L51

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

theorem GroundTheory.ProfCoh.intValuation_smulPlace (σ : G) (w : HeightOneSpectrum B) (r : B) :
    (smulPlace σ w).intValuation (σ • r) = w.intValuation r := by sorry
