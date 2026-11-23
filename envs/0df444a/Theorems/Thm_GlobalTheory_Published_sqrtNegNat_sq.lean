-- Prove2me | Theorems.Thm_GlobalTheory_Published_sqrtNegNat_sq
-- name    : GlobalTheory.Published.sqrtNegNat_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:43:09.621637+00:00
-- url     : https://prove2.me/theorems/8013b138-ab22-4ec7-ac6a-469c7283965f
-- title:
--   Published: sqrt Neg Nat sq
-- statement:
--   The Published construction uses the sqrt Neg Nat sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/CmCurveGoodOutsidePrimePremises.lean#L42-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/CmCurveGoodOutsidePrimePremises.lean#L42-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDiscreteValuationRingValuationSubringAtPrime
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_ComplexMultiplicationJPremises
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__CmCurveGoodOutsidePrimePremises_e87ddea43482082e
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain WeierstrassCurve
open scoped nonZeroDivisors IntermediateField
open GlobalTheory GlobalTheory.Published

theorem GlobalTheory.Published.sqrtNegNat_sq (p : ℕ) : sqrtNegNat p ^ 2 = -(p : ℂ) := by sorry
