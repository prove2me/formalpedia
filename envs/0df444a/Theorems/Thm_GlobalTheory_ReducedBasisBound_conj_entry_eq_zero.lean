-- Prove2me | Theorems.Thm_GlobalTheory_ReducedBasisBound_conj_entry_eq_zero
-- name    : GlobalTheory.ReducedBasisBound.conj_entry_eq_zero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T19:18:32.839248+00:00
-- url     : https://prove2.me/theorems/86beab1d-50c7-418c-8f1e-cf3ef6693f32
-- title:
--   Reduced Basis Bound: conj entry eq zero
-- statement:
--   The Reduced Basis Bound construction uses the conj entry eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ReducedBasisIntegralConjEntriesBounded.lean#L87-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ReducedBasisIntegralConjEntriesBounded.lean#L87-L121

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_UnipotentUpperInvUpperTriangularBounded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ReducedBasisIntegralConjEntriesBounded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open GlobalTheory GlobalTheory.ReducedBasisBound
variable {N : ℕ} {C₁ Cm T : ℝ} {a : Fin N → ℝ} {n m Z : Matrix (Fin N) (Fin N) ℝ}

theorem GlobalTheory.ReducedBasisBound.conj_entry_eq_zero (hC : 1 ≤ C₁) (ha : ∀ i, 0 < a i) (hle : ∀ i j, i ≤ j → a i ≤ C₁ * a j)
    (hnm : n * m = 1) (hn_low : ∀ i j, j < i → n i j = 0) (hm_low : ∀ i j, j < i → m i j = 0)
    (M' : Matrix (Fin N) (Fin N) ℤ)
    (h2 : diagonal a * n * M'.map (Int.cast : ℤ → ℝ) = Zᵀ * diagonal a * n)
    (ε : ℝ) (hA : ∀ i j, a i ≤ ε * a j → M' j i = 0) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ * C₁ ^ 2 = ε) :
    ∀ i j, a i ≤ δ * a j → Z i j = 0 := by sorry
