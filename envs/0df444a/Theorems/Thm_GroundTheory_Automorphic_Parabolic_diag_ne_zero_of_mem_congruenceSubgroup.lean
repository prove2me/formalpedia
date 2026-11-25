-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_diag_ne_zero_of_mem_congruenceSubgroup
-- name    : GroundTheory.Automorphic.Parabolic.diag_ne_zero_of_mem_congruenceSubgroup
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:20:06.34853+00:00
-- url     : https://prove2.me/theorems/f075181f-fa65-4361-9bb1-f4d0eaf4ccd9
-- title:
--   Parabolic: diag ne zero of mem congruence Subgroup
-- statement:
--   The Parabolic construction uses the diag ne zero of mem congruence Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/IwahoriFactorization.lean#L241-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/IwahoriFactorization.lean#L241-L244

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

theorem GroundTheory.Automorphic.Parabolic.diag_ne_zero_of_mem_congruenceSubgroup {m : ℕ} (hm : 1 ≤ m) {h : GL (Fin n) F}
    (hh : h ∈ congruenceSubgroup F n m) (a : Fin n) : h a a ≠ 0 := by sorry
