-- Prove2me | Theorems.Thm_GlobalTheory_WachFree_basis_of_baseChange
-- name    : GlobalTheory.WachFree.basis_of_baseChange
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:14:00.836796+00:00
-- url     : https://prove2.me/theorems/1fa3ae6f-9891-407a-9d77-813511ef2338
-- title:
--   Wach Free: basis of base Change
-- statement:
--   The Wach Free construction uses the basis of base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MemXSmulOfProjective.lean#L112-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MemXSmulOfProjective.lean#L112-L166

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

theorem GlobalTheory.WachFree.basis_of_baseChange {ι R N E D : Type} [Finite ι] [CommRing R] [IsLocalRing R]
    [AddCommGroup N] [Module (ι → R) N] [Module.Finite (ι → R) N] [Module R N]
    [IsScalarTower R (ι → R) N] [Module.Flat R N] [CommRing E] [Algebra (ι → R) E]
    (hE : Function.Injective (algebraMap (ι → R) E)) [AddCommGroup D] [Module E D]
    [Module (ι → R) D] [IsScalarTower (ι → R) E D] [Module.Free E D] (f : N →ₗ[ι → R] D)
    (hf : IsBaseChange E f) : Nonempty (Module.Basis (Fin (Module.finrank E D)) (ι → R) N) := by sorry
