-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_prepV_sub_bd
-- name    : GlobalTheory.PMonE.prepV_sub_bd
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:39:34.690516+00:00
-- url     : https://prove2.me/theorems/bfacd9de-fd20-4aa6-913b-fc27b343e04c
-- title:
--   PMon E: prep V sub bd
-- statement:
--   The PMon E construction uses the prep V sub bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdditiveSystemPreparationNormalFormOne.lean#L77-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdditiveSystemPreparationNormalFormOne.lean#L77-L97

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemPreparationNormalFormOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE
open Finset
variable {F : Type} [NormedField F] {m : Type} [Fintype m]
variable [IsUltrametricDist F]

theorem GlobalTheory.PMonE.prepV_sub_bd (p : ℕ) [Fact p.Prime] [CharP F p] {e D : ℕ} {M : ℕ → Matrix m m F} {δ ε : ℝ} (hδ : 0 ≤ δ)
    (hε : 0 ≤ ε) (hM : ∀ n, 2 ≤ n → n ≤ D → PrepBd δ (M n)) {A B : Matrix m m F} (hA : PrepBd 1 A)
    (hB : PrepBd 1 B) (h : PrepBd ε (A - B)) :
    ∀ k n, 1 ≤ n → n + k ≤ D → PrepBd (δ * ε) (prepV (p ^ e) M A k n - prepV (p ^ e) M B k n) := by sorry
