-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_jacquetMap_mk
-- name    : GroundTheory.Automorphic.Parabolic.jacquetMap_mk
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:13:19.205057+00:00
-- url     : https://prove2.me/theorems/7117d682-2118-4768-912b-52b34f570bc0
-- title:
--   Parabolic: jacquet Map mk
-- statement:
--   The Parabolic construction uses the jacquet Map mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolic.lean#L196-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolic.lean#L196-L198

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_Induction
import Definitions.Def_GroundTheory_AutomorphicForms_InductionJacquet
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicLocal
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
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
open Matrix Iwasawa GLnLocal Topology Filter Set MeasureTheory Measure
open scoped NNReal
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ) {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {F n β}
variable {V : Type*} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) F) V)
variable {π} {V' : Type*} [AddCommGroup V'] [Module ℂ V'] {π' : Representation ℂ (GL (Fin n) F) V'}
  {V'' : Type*} [AddCommGroup V''] [Module ℂ V''] {π'' : Representation ℂ (GL (Fin n) F) V''}

theorem GroundTheory.Automorphic.Parabolic.jacquetMap_mk (f : Representation.IntertwiningMap π π') (v : V) :
    jacquetMap F n β f (Representation.Coinvariants.mk _ v) =
      Representation.Coinvariants.mk _ (f v) := by sorry
