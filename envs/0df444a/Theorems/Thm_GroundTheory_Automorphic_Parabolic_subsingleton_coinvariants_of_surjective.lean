-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_subsingleton_coinvariants_of_surjective
-- name    : GroundTheory.Automorphic.Parabolic.subsingleton_coinvariants_of_surjective
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:47:40.343797+00:00
-- url     : https://prove2.me/theorems/fa8baac1-3312-5ab1-a710-a246db151043
-- title:
--   Parabolic: subsingleton coinvariants of surjective
-- statement:
--   The Parabolic construction uses the subsingleton coinvariants of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/JacquetAdmissible.lean#L233-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/JacquetAdmissible.lean#L233-L254

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

theorem GroundTheory.Automorphic.Parabolic.subsingleton_coinvariants_of_surjective {W : Type*} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} {H : Subgroup G}
    (f : Representation.IntertwiningMap ρ σ) (hf : Function.Surjective f)
    (h : Subsingleton (Representation.Coinvariants (ρ.comp H.subtype))) :
    Subsingleton (Representation.Coinvariants (σ.comp H.subtype)) := by sorry
