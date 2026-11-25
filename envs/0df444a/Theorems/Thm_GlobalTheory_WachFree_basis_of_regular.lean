-- Prove2me | Theorems.Thm_GlobalTheory_WachFree_basis_of_regular
-- name    : GlobalTheory.WachFree.basis_of_regular
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:29:31.280445+00:00
-- url     : https://prove2.me/theorems/08d1ca28-0f15-4f80-976e-49ffa01c5650
-- title:
--   Wach Free: basis of regular
-- statement:
--   The Wach Free construction uses the basis of regular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MemXSmulOfProjective.lean#L168-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MemXSmulOfProjective.lean#L168-L182

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

theorem GlobalTheory.WachFree.basis_of_regular {ι O N E D : Type} [Finite ι] [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [AddCommGroup N] [Module (ι → O⟦X⟧) N] [Module.Finite (ι → O⟦X⟧) N]
    [CommRing E] [Algebra (ι → O⟦X⟧) E]
    (hE : Function.Injective (algebraMap (ι → O⟦X⟧) E)) [AddCommGroup D] [Module E D]
    [Module (ι → O⟦X⟧) D] [IsScalarTower (ι → O⟦X⟧) E D] [Module.Free E D]
    (f : N →ₗ[ι → O⟦X⟧] D) (hf : IsBaseChange E f) (c : O) (hc : c ≠ 0) (hc' : ¬ IsUnit c)
    (hX : IsSMulRegular N (fun _ => X : ι → O⟦X⟧))
    (h : ∀ x y : N, (fun _ => C c : ι → O⟦X⟧) • x = (fun _ => X : ι → O⟦X⟧) • y →
      ∃ z : N, x = (fun _ => X : ι → O⟦X⟧) • z) :
    Nonempty (Module.Basis (Fin (Module.finrank E D)) (ι → O⟦X⟧) N) := by sorry
