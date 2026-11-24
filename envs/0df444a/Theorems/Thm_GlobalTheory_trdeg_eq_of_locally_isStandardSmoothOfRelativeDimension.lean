-- Prove2me | Theorems.Thm_GlobalTheory_trdeg_eq_of_locally_isStandardSmoothOfRelativeDimension
-- name    : GlobalTheory.trdeg_eq_of_locally_isStandardSmoothOfRelativeDimension
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:25:14.50667+00:00
-- url     : https://prove2.me/theorems/13a5c50b-383d-4356-a335-523ca6614e8e
-- title:
--   Global Theory: trdeg eq of locally is Standard Smooth Of Relative Dimension
-- statement:
--   The Global Theory construction uses the trdeg eq of locally is Standard Smooth Of Relative Dimension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/TrdegEqOfLocallyIsStandardSmoothOfRelativeDimens.lean#L11-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/TrdegEqOfLocallyIsStandardSmoothOfRelativeDimens.lean#L11-L38

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNeZeroIsStandardSmoothOfRelativeDimension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_TrdegEqOfLocallyIsStandardSmoothOfRelativeDimens
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem GlobalTheory.trdeg_eq_of_locally_isStandardSmoothOfRelativeDimension {K B : Type} [Field K]
    [CommRing B] [IsDomain B] [Algebra K B] {g : ℕ}
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension g) (algebraMap K B)) :
    Algebra.trdeg K B = g := by sorry
