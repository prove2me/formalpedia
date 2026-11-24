-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SiegelChar_finite_nonunit
-- name    : GlobalTheory.CompanionTheory.SiegelChar.finite_nonunit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:09:49.64601+00:00
-- url     : https://prove2.me/theorems/b68a0aa6-39b5-4cd9-8f70-efe7aea4b017
-- title:
--   Siegel Char: finite nonunit
-- statement:
--   The Siegel Char construction uses the finite nonunit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/SplitQuadraticAlgebraOrder.lean#L213-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/SplitQuadraticAlgebraOrder.lean#L213-L241

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_SplitQuadraticAlgebraOrder
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix ValuativeRel GlobalTheory.WeilM MeasureTheory
open scoped ComplexConjugate NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegelChar

theorem GlobalTheory.CompanionTheory.SiegelChar.finite_nonunit {F : Type} [Field F] {E : Type} [CommRing E] [Algebra F E] [Module.Finite F E]
    (p : Polynomial E) (τ : E) (h : IsUnit (p.eval τ)) : {t : F | ¬ IsUnit (p.eval (algebraMap F E t))}.Finite := by sorry
