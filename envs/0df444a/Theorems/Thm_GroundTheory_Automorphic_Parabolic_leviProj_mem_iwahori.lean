-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_leviProj_mem_iwahori
-- name    : GroundTheory.Automorphic.Parabolic.leviProj_mem_iwahori
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:20:05.421554+00:00
-- url     : https://prove2.me/theorems/5b9a463b-c083-410d-9aec-0511a572d283
-- title:
--   Parabolic: levi Proj mem iwahori
-- statement:
--   The Parabolic construction uses the levi Proj mem iwahori property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/IwahoriFactorization.lean#L291-L308
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/IwahoriFactorization.lean#L291-L308

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
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
local notation "ϖ" => ((GLnLocal.uniformizer F : 𝒪[F]) : F)

theorem GroundTheory.Automorphic.Parabolic.leviProj_mem_iwahori {p : GL (Fin n) F} (hp : p ∈ blockUpper F n β)
    (hpI : p ∈ iwahori F n) :
    ((leviProj F n β ⟨p, hp⟩ : levi F n β) : GL (Fin n) F) ∈ iwahori F n := by sorry
