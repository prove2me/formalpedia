-- Prove2me | Theorems.Thm_GlobalTheory_FieldDimCoheight_coheight_add_dim_closure_eq
-- name    : GlobalTheory.FieldDimCoheight.coheight_add_dim_closure_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:56:22.809567+00:00
-- url     : https://prove2.me/theorems/772b09dd-1338-4c9d-8f03-6a473f4862ec
-- title:
--   Field Dim Coheight: coheight add dim closure eq
-- statement:
--   The Field Dim Coheight construction uses the coheight add dim closure eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoheightEqOneIffClosureDimProjective.lean#L17-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoheightEqOneIffClosureDimProjective.lean#L17-L54

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TopologicalKrullDimEqOfOpenImmersionIntegralSche
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClosedComplementDimBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoheightEqOneIffClosureDimProjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory GlobalTheory.FieldDimCoheight

theorem GlobalTheory.FieldDimCoheight.coheight_add_dim_closure_eq (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp F) [LocallyOfFiniteType p] (z : X) :
    (Order.coheight z : WithBot ℕ∞) + topologicalKrullDim (closure ({z} : Set X)) =
      topologicalKrullDim X := by sorry
