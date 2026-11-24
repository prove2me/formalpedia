-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_sPicMk_eq_zero_iff
-- name    : GroundTheory.ProfCoh.sPicMk_eq_zero_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:41.334376+00:00
-- url     : https://prove2.me/theorems/bb6bad49-a8f7-49d9-aba8-d870ba6c1a33
-- title:
--   Prof Coh: s Pic Mk eq zero iff
-- statement:
--   The Prof Coh construction uses the s Pic Mk eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/SPicDefs.lean#L72-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/SPicDefs.lean#L72-L74

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

theorem GroundTheory.ProfCoh.sPicMk_eq_zero_iff (D : sDivisor S) : sPicMk S D = 0 ↔ ∃ x : Fˣ, divS S (Additive.ofMul x) = D := by sorry
