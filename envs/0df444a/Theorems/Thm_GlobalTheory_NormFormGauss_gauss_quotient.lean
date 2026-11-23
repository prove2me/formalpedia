-- Prove2me | Theorems.Thm_GlobalTheory_NormFormGauss_gauss_quotient
-- name    : GlobalTheory.NormFormGauss.gauss_quotient
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:38.636221+00:00
-- url     : https://prove2.me/theorems/163703f2-203d-4873-a57e-67c1b10a0dad
-- title:
--   Norm Form Gauss: gauss quotient
-- statement:
--   The Norm Form Gauss construction uses the gauss quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SumEqZeroAddUnits.lean#L168-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SumEqZeroAddUnits.lean#L168-L206

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumEqZeroAddUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.NormFormGauss

theorem GlobalTheory.NormFormGauss.gauss_quotient : ∀ {R : Type} [CommRing R] (σ : R →+* R) (w : R), (∀ r, σ (σ r) = r) → w + σ w = 1 → ∀ P : Ideal R, P.IsMaximal → Finite (R ⧸ P) → (∀ r ∈ P, σ r ∈ P) → (∃ r, σ r - r ∉ P) → ∀ χ : R → ℂ, (∀ s t, χ (s + t) = χ s * χ t) → χ 0 = 1 → (∀ r ∈ P, χ r = 1) → (∀ t, χ (σ t) = χ t) → (∃ t, χ t ≠ 1) → (∑ᶠ q : R ⧸ P, χ (w * (Quotient.out q : R) * σ (Quotient.out q : R))) = -(Real.sqrt (Nat.card (R ⧸ P)) : ℂ) := by sorry
