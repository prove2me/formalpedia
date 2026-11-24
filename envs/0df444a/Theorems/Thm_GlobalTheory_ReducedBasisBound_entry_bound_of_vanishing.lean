-- Prove2me | Theorems.Thm_GlobalTheory_ReducedBasisBound_entry_bound_of_vanishing
-- name    : GlobalTheory.ReducedBasisBound.entry_bound_of_vanishing
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:18:37.493526+00:00
-- url     : https://prove2.me/theorems/a8dee20b-a21d-49ad-b728-a257a2b03217
-- title:
--   Reduced Basis Bound: entry bound of vanishing
-- statement:
--   The Reduced Basis Bound construction uses the entry bound of vanishing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ReducedBasisIntegralConjEntriesBounded.lean#L123-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ReducedBasisIntegralConjEntriesBounded.lean#L123-L160

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

theorem GlobalTheory.ReducedBasisBound.entry_bound_of_vanishing (hC : 1 ≤ C₁) (hCm : 0 ≤ Cm) (hT : 0 ≤ T) (ha : ∀ i, 0 < a i)
    (hmn : m * n = 1) (hn : ∀ i j, |n i j| ≤ C₁) (hm : ∀ i j, |m i j| ≤ Cm) (hZ : ∀ i j, |Z i j| ≤ T)
    (M : Matrix (Fin N) (Fin N) ℤ)
    (h1 : diagonal a * n * M.map (Int.cast : ℤ → ℝ) = Z * diagonal a * n)
    (δ : ℝ) (hδ : 0 < δ) (hB : ∀ i j, a i ≤ δ * a j → Z i j = 0) :
    ∀ i j, |(M i j : ℝ)| ≤ N * (Cm * (N * (T * C₁ / δ))) := by sorry
