-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_gsBaseChange_toMulEquiv
-- name    : GroundTheory.ProfCoh.gsBaseChange_toMulEquiv
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:02:29.849971+00:00
-- url     : https://prove2.me/theorems/842d7423-7c40-5ad6-acd2-f38d7506b061
-- title:
--   Prof Coh: gs Base Change to Mul Equiv
-- statement:
--   The Prof Coh construction uses the gs Base Change to Mul Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/BaseChangeDefs.lean#L311-L313
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/BaseChangeDefs.lean#L311-L313

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_BaseChangeDefs
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
open NumberField IsDedekindDomain
universe u
noncomputable section
variable {F L Ω : Type u} [Field F] [NumberField F] [Field L] [NumberField L] [Field Ω]
  [Algebra F L] [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω] [IsGalois F Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F)))
  (hL : ∀ x : L, algebraMap L Ω x ∈ maxUnramifiedOutside F Ω S)

theorem GroundTheory.ProfCoh.gsBaseChange_toMulEquiv : (gsBaseChange S hL).toMulEquiv =
    fixingMulEquivOfRestrictScalarsEq (restrictScalars_maxUnramifiedOutside_eq S hL) := by sorry
