-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_subsingleton_coinvariants_jacquetRep
-- name    : GroundTheory.Automorphic.Parabolic.subsingleton_coinvariants_jacquetRep
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:47:12.348078+00:00
-- url     : https://prove2.me/theorems/95f027fc-8174-4a55-b253-1478410b00d6
-- title:
--   Parabolic: subsingleton coinvariants jacquet Rep
-- statement:
--   The Parabolic construction uses the subsingleton coinvariants jacquet Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/JacquetAdmissible.lean#L156-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/JacquetAdmissible.lean#L156-L209

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
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}

theorem GroundTheory.Automorphic.Parabolic.subsingleton_coinvariants_jacquetRep {β γ : Fin n → ℕ}
    (hβγ : ∀ i j, β j < β i → γ j < γ i) (h : Subsingleton (JacquetModule F n γ π)) :
    Subsingleton (Representation.Coinvariants
      ((jacquetRep F n β π).comp (leviUnipotent F n β γ).subtype)) := by sorry
