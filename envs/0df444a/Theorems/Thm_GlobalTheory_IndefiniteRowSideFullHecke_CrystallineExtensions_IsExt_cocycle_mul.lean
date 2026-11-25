-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CrystallineExtensions_IsExt_cocycle_mul
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.IsExt.cocycle_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:10:35.274998+00:00
-- url     : https://prove2.me/theorems/11fe5147-3158-43c9-a0f5-8cbc5a059187
-- title:
--   Is Ext: cocycle mul
-- statement:
--   The Is Ext construction uses the cocycle mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/CrystallineExtensions.lean#L31-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/CrystallineExtensions.lean#L31-L39

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.IsExt.cocycle_mul {ρ : Representation LL G V} {ρ' : Representation LL G W} {i : V →ₗ[LL] W}
    {p : W →ₗ[LL] LL} (h : IsExt ρ ρ' i p) {c : G → V} (hc : IsCocycleOf ρ' i p c) (g k : G) :
    c (g * k) = c g + ρ g (c k) := by sorry
