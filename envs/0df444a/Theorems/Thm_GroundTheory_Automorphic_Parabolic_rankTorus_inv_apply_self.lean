-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_rankTorus_inv_apply_self
-- name    : GroundTheory.Automorphic.Parabolic.rankTorus_inv_apply_self
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:54:18.256531+00:00
-- url     : https://prove2.me/theorems/a08bc958-003d-4cc7-abd0-a259471b3cf3
-- title:
--   Parabolic: rank Torus inv apply self
-- statement:
--   The Parabolic construction uses the rank Torus inv apply self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SupercuspidalCoefficients.lean#L247-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SupercuspidalCoefficients.lean#L247-L252

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

theorem GroundTheory.Automorphic.Parabolic.rankTorus_inv_apply_self {α : Type*} [LinearOrder α] (β : Fin n → α) (e : ℕ)
    (i : Fin n) :
    ((rankTorus F n β e)⁻¹ : GL (Fin n) F) i i =
      (uniformizer F : F) ^ (((e * blockRank β i : ℕ) : ℤ)) := by sorry
