-- Prove2me | Theorems.Thm_GlobalTheory_FieldDimCoheight_eq_one_iff_of_add_eq
-- name    : GlobalTheory.FieldDimCoheight.eq_one_iff_of_add_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:55:37.087214+00:00
-- url     : https://prove2.me/theorems/5ef41e64-5844-40d1-8bb4-8aa53906cafa
-- title:
--   Field Dim Coheight: eq one iff of add eq
-- statement:
--   The Field Dim Coheight construction uses the eq one iff of add eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoheightEqOneIffClosureDimProjective.lean#L56-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoheightEqOneIffClosureDimProjective.lean#L56-L75

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

theorem GlobalTheory.FieldDimCoheight.eq_one_iff_of_add_eq {c : ℕ∞} {t : WithBot ℕ∞} {e : ℕ}
    (h : (c : WithBot ℕ∞) + t = (e + 1 : ℕ)) : c = 1 ↔ t = e := by sorry
