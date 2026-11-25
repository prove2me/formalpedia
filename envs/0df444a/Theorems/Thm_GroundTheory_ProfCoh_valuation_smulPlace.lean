-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_valuation_smulPlace
-- name    : GroundTheory.ProfCoh.valuation_smulPlace
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:51:03.644863+00:00
-- url     : https://prove2.me/theorems/c1d93499-e0e7-487b-8a61-920e095f3835
-- title:
--   Prof Coh: valuation smul Place
-- statement:
--   The Prof Coh construction uses the valuation smul Place property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/ValuationTransport.lean#L59-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/ValuationTransport.lean#L59-L66

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
variable {F M : Type*} [Field F] [Field M] [NumberField M] [Algebra F M]

theorem GroundTheory.ProfCoh.valuation_smulPlace (σ : Gal(M/F)) (w : HeightOneSpectrum (𝓞 M)) (x : M) :
    (smulPlace σ w).valuation M (σ x) = w.valuation M x := by sorry
