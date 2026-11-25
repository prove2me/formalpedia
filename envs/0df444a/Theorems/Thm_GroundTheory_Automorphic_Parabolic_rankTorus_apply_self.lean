-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_rankTorus_apply_self
-- name    : GroundTheory.Automorphic.Parabolic.rankTorus_apply_self
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:54:17.820551+00:00
-- url     : https://prove2.me/theorems/faf090a3-c5c4-461d-88aa-8ac0859fe9f4
-- title:
--   Parabolic: rank Torus apply self
-- statement:
--   The Parabolic construction uses the rank Torus apply self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SupercuspidalCoefficients.lean#L241-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SupercuspidalCoefficients.lean#L241-L245

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

theorem GroundTheory.Automorphic.Parabolic.rankTorus_apply_self {α : Type*} [LinearOrder α] (β : Fin n → α) (e : ℕ) (i : Fin n) :
    (rankTorus F n β e : GL (Fin n) F) i i =
      (uniformizer F : F) ^ (-((e * blockRank β i : ℕ) : ℤ)) := by sorry
