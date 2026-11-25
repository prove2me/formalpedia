-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_finset_of_isSupercuspidal
-- name    : GroundTheory.Automorphic.Parabolic.exists_finset_of_isSupercuspidal
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:54:37.35288+00:00
-- url     : https://prove2.me/theorems/ca03fd17-4486-45d3-a5a9-47f1e870391d
-- title:
--   Parabolic: exists finset of is Supercuspidal
-- statement:
--   The Parabolic construction uses the exists finset of is Supercuspidal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SupercuspidalCoefficients.lean#L80-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SupercuspidalCoefficients.lean#L80-L102

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_IwahoriFactorization
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SupercuspidalCoefficients
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
open scoped Pointwise
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {π : Representation ℂ (GL (Fin n) F) V}

theorem GroundTheory.Automorphic.Parabolic.exists_finset_of_isSupercuspidal (hsc : IsSupercuspidal π) {S : Finset (Fin n)}
    (hS : ∃ i j, i ∈ S ∧ j ∉ S) (w : V) :
    ∃ U : Finset (GL (Fin n) F), (∀ u ∈ U, u ∈ unipotentRadical F n (splitFun S)) ∧
      w ∈ Submodule.span ℂ {y | ∃ u ∈ U, ∃ x, y = π u x - x} := by sorry
