-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SplitUnique_hTens_eq_zero
-- name    : GlobalTheory.CompanionTheory.SplitUnique.hTens_eq_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:14:43.546636+00:00
-- url     : https://prove2.me/theorems/2e1c115a-917a-4f9c-95a7-047d1b6a9371
-- title:
--   Split Unique: h Tens eq zero
-- statement:
--   The Split Unique construction uses the h Tens eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/LagrangianStabilizerCharacterTrivial.lean#L28-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/LagrangianStabilizerCharacterTrivial.lean#L28-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsEqMulApplyZero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_SplitQuadraticAlgebraOrder
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsInvariantForm
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_LagrangianStabilizerCharacterTrivial
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SplitUnique
variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
  {α β : Type} [Fintype α] [Fintype β]

theorem GlobalTheory.CompanionTheory.SplitUnique.hTens_eq_zero (JA : Matrix α α E) {JB : Matrix β β E} {ν : Type} [Fintype ν] {Cy : Matrix β ν E}
    (h : Cyᵀ * JB * Cy.map c = 0) (z z' : Matrix α ν E) : hTens c JA JB (z * Cyᵀ) (z' * Cyᵀ) = 0 := by sorry
