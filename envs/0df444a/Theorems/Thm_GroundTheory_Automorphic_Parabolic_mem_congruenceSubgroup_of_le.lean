-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_congruenceSubgroup_of_le
-- name    : GroundTheory.Automorphic.Parabolic.mem_congruenceSubgroup_of_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:19:38.508019+00:00
-- url     : https://prove2.me/theorems/45d3edfa-685e-495c-842c-5025a8df2179
-- title:
--   Parabolic: mem congruence Subgroup of le
-- statement:
--   The Parabolic construction uses the mem congruence Subgroup of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/IwahoriFactorization.lean#L218-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/IwahoriFactorization.lean#L218-L233

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

theorem GroundTheory.Automorphic.Parabolic.mem_congruenceSubgroup_of_le {m : ℕ} {g : GL (Fin n) F}
    (h1 : ∀ i j, valuation F (g i j - (1 : Matrix (Fin n) (Fin n) F) i j) ≤ valuation F ϖ ^ m)
    (h2 : ∀ i j, valuation F ((g⁻¹ : GL (Fin n) F) i j - (1 : Matrix (Fin n) (Fin n) F) i j) ≤
      valuation F ϖ ^ m) :
    g ∈ congruenceSubgroup F n m := by sorry
