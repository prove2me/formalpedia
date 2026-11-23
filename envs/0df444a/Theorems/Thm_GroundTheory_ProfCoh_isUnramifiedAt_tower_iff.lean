-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_isUnramifiedAt_tower_iff
-- name    : GroundTheory.ProfCoh.isUnramifiedAt_tower_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:51.178122+00:00
-- url     : https://prove2.me/theorems/bcf0d60f-feef-40bf-a66d-eff694aa737c
-- title:
--   Prof Coh: is Unramified At tower iff
-- statement:
--   The Prof Coh construction uses the is Unramified At tower iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/Ramification.lean#L12-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/Ramification.lean#L12-L17

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_Ramification
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
variable {F L M : Type*} [Field F] [Field L] [Field M] [NumberField F] [NumberField L]
  [NumberField M] [Algebra F L] [Algebra L M] [Algebra F M] [IsScalarTower F L M]

theorem GroundTheory.ProfCoh.isUnramifiedAt_tower_iff (Q : Ideal (𝓞 M)) [Q.IsPrime] :
    Algebra.IsUnramifiedAt (𝓞 F) Q ↔
      Algebra.IsUnramifiedAt (𝓞 F) (Q.under (𝓞 L)) ∧ Algebra.IsUnramifiedAt (𝓞 L) Q := by sorry
