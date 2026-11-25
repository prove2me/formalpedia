-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CrystallineExtensions_extRep_isExt
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.extRep_isExt
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:10:06.583249+00:00
-- url     : https://prove2.me/theorems/1d2fbf1e-e931-4e0a-8fa0-efb5b79d8488
-- title:
--   Crystalline Extensions: ext Rep is Ext
-- statement:
--   The Crystalline Extensions construction uses the ext Rep is Ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/CrystallineExtensions.lean#L65-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/CrystallineExtensions.lean#L65-L71

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MkMemAdmissibleAtIffCocycle
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_CrystallineExtensions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions TensorProduct
variable {G : Type} [Group G] {LL : Type} [Field LL] {V W : Type} [AddCommGroup V] [Module LL V]
  [AddCommGroup W] [Module LL W]
variable [TopologicalSpace G] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]

theorem GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.extRep_isExt (ρ : Representation LL G V) (c : ↥(continuousCocycles ρ)) :
    IsExt ρ (extRep ρ c) (LinearMap.inl LL V LL) (LinearMap.snd LL V LL) ∧
      IsCocycleOf (extRep ρ c) (LinearMap.inl LL V LL) (LinearMap.snd LL V LL) (c : G → V) := by sorry
