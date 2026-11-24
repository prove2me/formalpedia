-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WeilOneMember_isHerm_dbl
-- name    : GlobalTheory.CompanionTheory.WeilOneMember.isHerm_dbl
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:38:54.131797+00:00
-- url     : https://prove2.me/theorems/ea9453fd-f714-45c4-9f6d-3d36f969b535
-- title:
--   Weil One Member: is Herm dbl
-- statement:
--   The Weil One Member construction uses the is Herm dbl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/DblCoordUnique.lean#L15-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/DblCoordUnique.lean#L15-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_LagrangianStabilizerCharacterTrivial
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_DblCoordUnique
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WeilOneMember
variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem GlobalTheory.CompanionTheory.WeilOneMember.isHerm_dbl {JB : Matrix β β E} (h : IsHerm c JB) : IsHerm c (dbl JB) := by sorry
