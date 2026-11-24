-- Prove2me | Theorems.Thm_GlobalTheory_UnifTransport_hermForm_eq_of_im
-- name    : GlobalTheory.UnifTransport.hermForm_eq_of_im
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:24:55.804867+00:00
-- url     : https://prove2.me/theorems/60e47f05-ce75-4d38-9e64-27ee28136abe
-- title:
--   Unif Transport: herm Form eq of im
-- statement:
--   The Unif Transport construction uses the herm Form eq of im property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TransportThetaLevelUniformisationCoordinates.lean#L32-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TransportThetaLevelUniformisationCoordinates.lean#L32-L75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsHolUnifReparam
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TransportThetaLevelUniformisationCoordinates
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
open GlobalTheory GlobalTheory.UnifTransport

theorem GlobalTheory.UnifTransport.hermForm_eq_of_im {g : ℕ} (H H' : Matrix (Fin g) (Fin g) ℂ)
    (h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (S : Set (Fin g → ℂ)) (hS : Submodule.span ℝ S = ⊤)
    (him : ∀ x ∈ S, ∀ y ∈ S, (hermForm H' (h x) (h y)).im = (hermForm H x y).im) (z w : Fin g → ℂ) :
    hermForm H' (h z) (h w) = hermForm H z w := by sorry
