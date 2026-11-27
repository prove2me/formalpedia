-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_jacquetFixedMap_surjective_iwahori
-- name    : GroundTheory.Automorphic.Parabolic.jacquetFixedMap_surjective_iwahori
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:53:59.301198+00:00
-- url     : https://prove2.me/theorems/9fd00b84-4293-5888-a748-df59cd560191
-- title:
--   Parabolic: jacquet Fixed Map surjective iwahori
-- statement:
--   The Parabolic construction uses the jacquet Fixed Map surjective iwahori property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/IwahoriFactorization.lean#L528-L531
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/IwahoriFactorization.lean#L528-L531

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
variable {β}

theorem GroundTheory.Automorphic.Parabolic.jacquetFixedMap_surjective_iwahori (hπ : IsAdmissible π) (hβ : Monotone β) :
    Function.Surjective (jacquetFixedMap F n β π (iwahori F n)) := by sorry
