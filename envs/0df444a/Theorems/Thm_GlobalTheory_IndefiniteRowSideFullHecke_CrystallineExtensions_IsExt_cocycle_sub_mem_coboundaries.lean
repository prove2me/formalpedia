-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CrystallineExtensions_IsExt_cocycle_sub_mem_coboundaries
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.IsExt.cocycle_sub_mem_coboundaries
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:16:44.574371+00:00
-- url     : https://prove2.me/theorems/5ae4bada-e8dc-5999-9d8c-09958971ac1c
-- title:
--   Is Ext: cocycle sub mem coboundaries
-- statement:
--   The Is Ext construction uses the cocycle sub mem coboundaries property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/CrystallineExtensions.lean#L41-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/CrystallineExtensions.lean#L41-L50

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.IsExt.cocycle_sub_mem_coboundaries {ρ : Representation LL G V} {ρ' : Representation LL G W} {i : V →ₗ[LL] W}
    {p : W →ₗ[LL] LL} (h : IsExt ρ ρ' i p) {c c' : G → V} (hc : IsCocycleOf ρ' i p c)
    (hc' : IsCocycleOf ρ' i p c') : c - c' ∈ B1 ρ := by sorry
