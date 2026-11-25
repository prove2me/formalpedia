-- Prove2me | Theorems.Thm_GlobalTheory_FieldDimCoheight_coheight_eq_one_iff
-- name    : GlobalTheory.FieldDimCoheight.coheight_eq_one_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:56:12.936432+00:00
-- url     : https://prove2.me/theorems/e4eae42d-013e-415f-a0d8-204010463d97
-- title:
--   Field Dim Coheight: coheight eq one iff
-- statement:
--   The Field Dim Coheight construction uses the coheight eq one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoheightEqOneIffClosureDimProjective.lean#L77-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoheightEqOneIffClosureDimProjective.lean#L77-L85

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

theorem GlobalTheory.FieldDimCoheight.coheight_eq_one_iff : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp F)
    (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ z : X,
    Order.coheight z = 1 ↔ topologicalKrullDim (closure ({z} : Set X)) = e := by sorry
