-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_nontrivial_jacquetModule_const
-- name    : GroundTheory.Automorphic.Parabolic.nontrivial_jacquetModule_const
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:54:03.756145+00:00
-- url     : https://prove2.me/theorems/8bd60ee3-cafa-4c7a-b2a5-ce5cf2ac8111
-- title:
--   Parabolic: nontrivial jacquet Module const
-- statement:
--   The Parabolic construction uses the nontrivial jacquet Module const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/JacquetAdmissible.lean#L317-L331
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/JacquetAdmissible.lean#L317-L331

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

theorem GroundTheory.Automorphic.Parabolic.nontrivial_jacquetModule_const [Nontrivial V] :
    Nontrivial (JacquetModule F n (fun _ : Fin n => (0 : ℕ)) π) := by sorry
