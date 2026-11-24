-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SiegelChar_finite_nonunit_matrix
-- name    : GlobalTheory.CompanionTheory.SiegelChar.finite_nonunit_matrix
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:39.167323+00:00
-- url     : https://prove2.me/theorems/d422ee36-b9b4-499b-bee9-c5e1f653ab5e
-- title:
--   Siegel Char: finite nonunit matrix
-- statement:
--   The Siegel Char construction uses the finite nonunit matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/SplitQuadraticAlgebraOrder.lean#L243-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/SplitQuadraticAlgebraOrder.lean#L243-L261

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

theorem GlobalTheory.CompanionTheory.SiegelChar.finite_nonunit_matrix {F : Type} [Field F] {E : Type} [CommRing E] [Algebra F E] [Module.Finite F E]
    {β : Type} [Fintype β] [DecidableEq β] (A B D : Matrix β β E) (τ : E) (h : IsUnit (A + τ • B + (τ * τ) • D)) :
    {t : F | ¬ IsUnit (A + algebraMap F E t • B + (algebraMap F E t * algebraMap F E t) • D)}.Finite := by sorry
