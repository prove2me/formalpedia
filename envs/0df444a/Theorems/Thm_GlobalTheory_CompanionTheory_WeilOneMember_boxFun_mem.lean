-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WeilOneMember_boxFun_mem
-- name    : GlobalTheory.CompanionTheory.WeilOneMember.boxFun_mem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:38:40.887382+00:00
-- url     : https://prove2.me/theorems/a2736049-b9bf-4029-9ca7-70d1c4026932
-- title:
--   Weil One Member: box Fun mem
-- statement:
--   The Weil One Member construction uses the box Fun mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/DblCoordUnique.lean#L38-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/DblCoordUnique.lean#L38-L66

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

theorem GlobalTheory.CompanionTheory.WeilOneMember.boxFun_mem {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {κ κ' : Type}
    {φ₁ : (κ → R) → ℂ} {φ₂ : (κ' → R) → ℂ} (h₁ : φ₁ ∈ SB (κ → R)) (h₂ : φ₂ ∈ SB (κ' → R)) :
    boxFun φ₁ φ₂ ∈ SB (κ ⊕ κ' → R) := by sorry
