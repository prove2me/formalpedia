-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_embedding_parabolicInd
-- name    : GroundTheory.Automorphic.Parabolic.exists_embedding_parabolicInd
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:47:42.913801+00:00
-- url     : https://prove2.me/theorems/9787efa5-7d8e-4a71-b747-ff0fddcb25a2
-- title:
--   Parabolic: exists embedding parabolic Ind
-- statement:
--   The Parabolic construction uses the exists embedding parabolic Ind property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/JacquetAdmissible.lean#L413-L463
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/JacquetAdmissible.lean#L413-L463

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
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
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set MeasureTheory Measure
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}

theorem GroundTheory.Automorphic.Parabolic.exists_embedding_parabolicInd [π.IsIrreducible] (hπ : IsSmooth π) :
    ∃ (β : Fin n → ℕ) (W : Type u) (_ : AddCommGroup W) (_ : Module ℂ W)
      (σ : Representation ℂ (levi F n β) W), σ.IsIrreducible ∧ IsSmooth σ ∧ IsCuspidal σ ∧
        IsAdmissible σ ∧ ∃ Φ : Representation.IntertwiningMap π (parabolicInd F n β σ),
          Function.Injective Φ := by sorry
