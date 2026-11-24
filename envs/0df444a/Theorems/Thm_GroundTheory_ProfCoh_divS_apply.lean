-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_divS_apply
-- name    : GroundTheory.ProfCoh.divS_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:48:22.193091+00:00
-- url     : https://prove2.me/theorems/802c8980-5a6c-490f-9b82-7960b0f88c76
-- title:
--   Prof Coh: div S apply
-- statement:
--   The Prof Coh construction uses the div S apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/SPicDefs.lean#L64-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/SPicDefs.lean#L64-L66

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
variable (S : Set (HeightOneSpectrum (𝓞 F)))

theorem GroundTheory.ProfCoh.divS_apply (x : Additive Fˣ) (v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}) :
    divS S x v = ordAt v.1 (Additive.toMul x) := by sorry
