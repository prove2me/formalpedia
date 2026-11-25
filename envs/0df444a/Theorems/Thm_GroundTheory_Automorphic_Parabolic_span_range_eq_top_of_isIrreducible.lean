-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_span_range_eq_top_of_isIrreducible
-- name    : GroundTheory.Automorphic.Parabolic.span_range_eq_top_of_isIrreducible
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:47:03.309836+00:00
-- url     : https://prove2.me/theorems/228ac9a5-b57f-4ba7-bb7b-6be9a889b6cf
-- title:
--   Parabolic: span range eq top of is Irreducible
-- statement:
--   The Parabolic construction uses the span range eq top of is Irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/JacquetAdmissible.lean#L217-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/JacquetAdmissible.lean#L217-L231

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
variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem GroundTheory.Automorphic.Parabolic.span_range_eq_top_of_isIrreducible {ρ : Representation ℂ G V} [ρ.IsIrreducible] {v : V}
    (hv : v ≠ 0) : Submodule.span ℂ (Set.range fun g : G => ρ g v) = ⊤ := by sorry
