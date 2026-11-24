-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WeilOneMember_exists_embed
-- name    : GlobalTheory.CompanionTheory.WeilOneMember.exists_embed
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:38:48.877287+00:00
-- url     : https://prove2.me/theorems/126d450a-fd3d-41bd-9b5f-26174b0b1b9c
-- title:
--   Weil One Member: exists embed
-- statement:
--   The Weil One Member construction uses the exists embed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/DblCoordUnique.lean#L22-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/DblCoordUnique.lean#L22-L34

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

theorem GlobalTheory.CompanionTheory.WeilOneMember.exists_embed {JB : Matrix β β E} (g : UG c JB) : ∃ gd : UG c (dbl JB),
    ((gd : GL (β ⊕ β) E) : Matrix (β ⊕ β) (β ⊕ β) E) = Matrix.fromBlocks ((g : GL β E) : Matrix β β E) 0 0 1 := by sorry
