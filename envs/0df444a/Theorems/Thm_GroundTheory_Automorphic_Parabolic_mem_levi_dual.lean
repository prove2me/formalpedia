-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_levi_dual
-- name    : GroundTheory.Automorphic.Parabolic.mem_levi_dual
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:20:43.05059+00:00
-- url     : https://prove2.me/theorems/adc084fd-c765-4826-8efa-9d9a147410fc
-- title:
--   Parabolic: mem levi dual
-- statement:
--   The Parabolic construction uses the mem levi dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/IwahoriFactorization.lean#L160-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/IwahoriFactorization.lean#L160-L163

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_IwahoriFactorization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set
variable {F : Type*} [Field F] {n : ℕ} {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {β}
variable (β)
variable {β}
variable (β)
variable {β}

theorem GroundTheory.Automorphic.Parabolic.mem_levi_dual {g : GL (Fin n) F} :
    g ∈ levi F n (OrderDual.toDual ∘ β) ↔ g ∈ levi F n β := by sorry
