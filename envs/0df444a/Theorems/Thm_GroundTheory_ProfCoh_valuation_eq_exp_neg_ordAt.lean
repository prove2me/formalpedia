-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_valuation_eq_exp_neg_ordAt
-- name    : GroundTheory.ProfCoh.valuation_eq_exp_neg_ordAt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:48:45.086674+00:00
-- url     : https://prove2.me/theorems/5c7ea283-82ec-4f67-aa05-6a7a2fbb630b
-- title:
--   Prof Coh: valuation eq exp neg ord At
-- statement:
--   The Prof Coh construction uses the valuation eq exp neg ord At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/SPicDefs.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/SPicDefs.lean#L29-L32

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

theorem GroundTheory.ProfCoh.valuation_eq_exp_neg_ordAt (v : HeightOneSpectrum (𝓞 F)) (x : Fˣ) :
    v.valuation F (x : F) = WithZero.exp (-ordAt v x) := by sorry
