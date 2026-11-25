-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_rankTorus_inv_conj_apply
-- name    : GroundTheory.Automorphic.Parabolic.rankTorus_inv_conj_apply
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:07:40.87698+00:00
-- url     : https://prove2.me/theorems/7c323cf3-902d-5f0a-9c87-704f07e1afec
-- title:
--   Parabolic: rank Torus inv conj apply
-- statement:
--   The Parabolic construction uses the rank Torus inv conj apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolicLocal.lean#L62-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolicLocal.lean#L62-L69

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicLocal
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
variable (F) (n : ℕ) {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {F n β}

theorem GroundTheory.Automorphic.Parabolic.rankTorus_inv_conj_apply (e : ℕ) (g : GL (Fin n) F) (i j : Fin n) :
    ((rankTorus F n β e)⁻¹ * g * rankTorus F n β e : GL (Fin n) F) i j =
      (GLnLocal.uniformizer F : F) ^ (((e * blockRank β i : ℕ) : ℤ) - ((e * blockRank β j : ℕ) : ℤ)) *
        g i j := by sorry
