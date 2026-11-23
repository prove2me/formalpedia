-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_coe_torsNRep_apply
-- name    : GroundTheory.ProfCoh.coe_torsNRep_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:58:19.334211+00:00
-- url     : https://prove2.me/theorems/8ea049b2-f7dd-4b6c-ac2e-181260c5fc92
-- title:
--   Prof Coh: coe tors NRep apply
-- statement:
--   The Prof Coh construction uses the coe tors NRep apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/AdditiveDefs.lean#L97-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/AdditiveDefs.lean#L97-L99

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveDefs
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
universe u v
open Representation
variable {Γ : Type*} [Group Γ]
variable (Γ) (A : Type*) [AddCommGroup A] [DistribMulAction Γ A] (n : ℕ)

theorem GroundTheory.ProfCoh.coe_torsNRep_apply (γ : Γ) (x : TorsN A n) :
    ((torsNRep Γ A n γ x : TorsN A n) : A) = γ • (x : A) := by sorry

attribute [defeq] GroundTheory.ProfCoh.coe_torsNRep_apply
