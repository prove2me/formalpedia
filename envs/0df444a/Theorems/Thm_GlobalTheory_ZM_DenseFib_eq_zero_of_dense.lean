-- Prove2me | Theorems.Thm_GlobalTheory_ZM_DenseFib_eq_zero_of_dense
-- name    : GlobalTheory.ZM.DenseFib.eq_zero_of_dense
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:14:23.372112+00:00
-- url     : https://prove2.me/theorems/33810e91-ee49-40b2-a6ac-2edebd80588c
-- title:
--   Dense Fib: eq zero of dense
-- statement:
--   The Dense Fib construction uses the eq zero of dense property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MemIdealOfOfDense.lean#L40-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MemIdealOfOfDense.lean#L40-L64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SecCoordBcScaleUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SectionCoordinateVectorExistsLocallyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MemIdealOfOfDense
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.DenseFib

theorem GlobalTheory.ZM.DenseFib.eq_zero_of_dense {A : Type} [CommRing A] [_root_.IsReduced A] (D : Set (Sp A)) (hD : Dense D) (a : A)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (κ : A →+* K), Set.range (spMap κ) ⊆ D → κ a = 0) :
    a = 0 := by sorry
