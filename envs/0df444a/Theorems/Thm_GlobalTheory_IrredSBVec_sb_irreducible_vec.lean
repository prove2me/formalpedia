-- Prove2me | Theorems.Thm_GlobalTheory_IrredSBVec_sb_irreducible_vec
-- name    : GlobalTheory.IrredSBVec.sb_irreducible_vec
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:21:34.618825+00:00
-- url     : https://prove2.me/theorems/035ebccf-5d08-4aac-93f4-5fe4caf06aaa
-- title:
--   Irred SBVec: sb irreducible vec
-- statement:
--   The Irred SBVec construction uses the sb irreducible vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzBruhatVectorIrreducibleTranslationsChara.lean#L36-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzBruhatVectorIrreducibleTranslationsChara.lean#L36-L110

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatMatrixTranslationModulationIrreduc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsNeZeroOfEventually
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzBruhatVectorIrreducibleTranslationsChara
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.IrredSBVec
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.IrredSBVec.sb_irreducible_vec : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    {κ : Type} [Fintype κ] (ψ0 : AddChar k ℂ), Continuous ψ0 →
    (∀ x : k, (∀ y ∈ 𝒪[k], ψ0 (x * y) = 1) ↔ x ∈ 𝒪[k]) →
    ∀ W : Submodule ℂ ((κ → k) → ℂ), W ≤ GlobalTheory.WeilM.SB (κ → k) →
    (∀ φ ∈ W, ∀ v : κ → k, (fun x => φ (x + v)) ∈ W) →
    (∀ φ ∈ W, ∀ y : κ → k, (fun x => ψ0 (x ⬝ᵥ y) * φ x) ∈ W) →
    ∀ φ₀ ∈ W, φ₀ ≠ 0 → W = GlobalTheory.WeilM.SB (κ → k) := by sorry
