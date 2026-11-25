-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_finset_span_jacquetRep
-- name    : GroundTheory.Automorphic.Parabolic.exists_finset_span_jacquetRep
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:46:11.127801+00:00
-- url     : https://prove2.me/theorems/24f1bedb-e899-5379-8de7-bb90aad2ef0f
-- title:
--   Parabolic: exists finset span jacquet Rep
-- statement:
--   The Parabolic construction uses the exists finset span jacquet Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/JacquetAdmissible.lean#L264-L315
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/JacquetAdmissible.lean#L264-L315

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

theorem GroundTheory.Automorphic.Parabolic.exists_finset_span_jacquetRep (hπ : IsSmooth π) {v : V}
    (hv : Submodule.span ℂ (Set.range fun g : GL (Fin n) F => π g v) = ⊤) :
    ∃ S : Finset (JacquetModule F n β π),
      Submodule.span ℂ {x | ∃ m, ∃ s ∈ S, x = jacquetRep F n β π m s} = ⊤ := by sorry
