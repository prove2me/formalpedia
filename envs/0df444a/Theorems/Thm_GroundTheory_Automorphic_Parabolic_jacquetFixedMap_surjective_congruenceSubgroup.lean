-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_jacquetFixedMap_surjective_congruenceSubgroup
-- name    : GroundTheory.Automorphic.Parabolic.jacquetFixedMap_surjective_congruenceSubgroup
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:20:45.824286+00:00
-- url     : https://prove2.me/theorems/9a484d1d-4a74-4c9d-9956-50e60e9466dc
-- title:
--   Parabolic: jacquet Fixed Map surjective congruence Subgroup
-- statement:
--   The Parabolic construction uses the jacquet Fixed Map surjective congruence Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/IwahoriFactorization.lean#L521-L524
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/IwahoriFactorization.lean#L521-L524

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
  {n : ℕ} {α : Type*} [LinearOrder α] (β : Fin n → α)
  {V : Type*} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}

theorem GroundTheory.Automorphic.Parabolic.jacquetFixedMap_surjective_congruenceSubgroup (hπ : IsAdmissible π) {m : ℕ} (hm : 1 ≤ m) :
    Function.Surjective (jacquetFixedMap F n β π (congruenceSubgroup F n m)) := by sorry
