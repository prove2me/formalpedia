-- Prove2me | Theorems.Thm_GlobalTheory_MultiHilbert_finrank_sup_add_finrank_colonX
-- name    : GlobalTheory.MultiHilbert.finrank_sup_add_finrank_colonX
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:29:17.5357+00:00
-- url     : https://prove2.me/theorems/ce392c75-9d46-4ba7-8421-5061da469587
-- title:
--   Multi Hilbert: finrank sup add finrank colon X
-- statement:
--   The Multi Hilbert construction uses the finrank sup add finrank colon X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsMultigradedHilbertPoly.lean#L246-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsMultigradedHilbertPoly.lean#L246-L292

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsMultigradedHilbertPoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MultiHilbert
open MvPolynomial
variable {K σ M : Type} [Field K] [AddCancelCommMonoid M] (w : σ → M)

theorem GlobalTheory.MultiHilbert.finrank_sup_add_finrank_colonX {I : Ideal (MvPolynomial σ K)}
    (hI : ∀ F ∈ I, ∀ n, weightedHomogeneousComponent w n F ∈ I) (i : σ) (n : M)
    [Module.Finite K (weightedHomogeneousSubmodule K w (n + w i))]
    [Module.Finite K (weightedHomogeneousSubmodule K w n)] :
    Module.finrank K ↥(weightedHomogeneousSubmodule K w (n + w i) ⊓
        (I ⊔ Ideal.span {X i}).restrictScalars K) +
      Module.finrank K ↥(weightedHomogeneousSubmodule K w n ⊓ (colonX I i).restrictScalars K) =
    Module.finrank K ↥(weightedHomogeneousSubmodule K w (n + w i) ⊓ I.restrictScalars K) +
      Module.finrank K ↥(weightedHomogeneousSubmodule K w n) := by sorry
