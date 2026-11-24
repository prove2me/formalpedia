-- Prove2me | Theorems.Thm_GlobalTheory_SiegelAction_act_complex
-- name    : GlobalTheory.SiegelAction.act_complex
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:11:32.142671+00:00
-- url     : https://prove2.me/theorems/0cffd950-47b5-46b4-a9c6-58add59fa93f
-- title:
--   Siegel Action: act complex
-- statement:
--   The Siegel Action construction uses the act complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SymplecticSiegelActionMemUpperHalfSpaceAndCocycl.lean#L78-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SymplecticSiegelActionMemUpperHalfSpaceAndCocycl.lean#L78-L148

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticSiegelActionMemUpperHalfSpaceAndCocycl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SiegelAction
open scoped ComplexOrder
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.SiegelAction.act_complex {A B C D τ : Matrix ι ι ℂ}
    (h : fromBlocks A B C D ∈ symplecticGroup ι ℂ) (hA : A.map conj = A) (hB : B.map conj = B)
    (hC : C.map conj = C) (hD : D.map conj = D) (hτ : τ ∈ Siegel ι) :
    (C * τ + D).det ≠ 0 ∧ (A * τ + B) * (C * τ + D)⁻¹ ∈ Siegel ι ∧ ((C * τ + D)⁻¹ * C).IsSymm ∧
      (C * τ + D)ᵀ * ((A * τ + B) * (C * τ + D)⁻¹).map (fun z => (z.im : ℂ)) *
        (C * τ + D).map conj = τ.map (fun z => (z.im : ℂ)) := by sorry
