-- Prove2me | Theorems.Thm_GlobalTheory_MultiHilbert_component_X_mul
-- name    : GlobalTheory.MultiHilbert.component_X_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:41:00.565232+00:00
-- url     : https://prove2.me/theorems/8f5a3d29-b28d-45a3-be68-4b33d6c67116
-- title:
--   Multi Hilbert: component X mul
-- statement:
--   The Multi Hilbert construction uses the component X mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsMultigradedHilbertPoly.lean#L189-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsMultigradedHilbertPoly.lean#L189-L205

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

theorem GlobalTheory.MultiHilbert.component_X_mul (i : σ) (n : M) (G : MvPolynomial σ K) :
    weightedHomogeneousComponent w (n + w i) (X i * G) =
      X i * weightedHomogeneousComponent w n G := by sorry
