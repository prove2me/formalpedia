-- Prove2me | Theorems.Thm_GlobalTheory_WachFree_free_of_regular
-- name    : GlobalTheory.WachFree.free_of_regular
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T02:54:18.453024+00:00
-- url     : https://prove2.me/theorems/7d18aa71-c8e9-554b-9223-acfbf64fb5b0
-- title:
--   Wach Free: free of regular
-- statement:
--   The Wach Free construction uses the free of regular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MemXSmulOfProjective.lean#L28-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MemXSmulOfProjective.lean#L28-L90

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DvrComplete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemXSmulOfProjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct
open GlobalTheory GlobalTheory.WachFree

theorem GlobalTheory.WachFree.free_of_regular {O M : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup M] [Module O⟦X⟧ M] [Module.Finite O⟦X⟧ M] (c : O) (hc : c ≠ 0) (hc' : ¬ IsUnit c)
    (hX : IsSMulRegular M (X : O⟦X⟧))
    (h : ∀ x y : M, (C c : O⟦X⟧) • x = (X : O⟦X⟧) • y → ∃ z : M, x = (X : O⟦X⟧) • z) :
    Module.Free O⟦X⟧ M := by sorry
