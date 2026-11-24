-- Prove2me | Theorems.Thm_GlobalTheory_KeyKa_KosGr_exact_dd
-- name    : GlobalTheory.KeyKa.KosGr.exact_dd
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:47:27.183451+00:00
-- url     : https://prove2.me/theorems/961dfb6f-ce01-4336-821f-cdeb13634c68
-- title:
--   Kos Gr: exact dd
-- statement:
--   The Kos Gr construction uses the exact dd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/KoszulExactOfGradedRegular.lean#L101-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/KoszulExactOfGradedRegular.lean#L101-L248

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_KoszulExactOfGradedRegular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.KeyKa GlobalTheory.KeyKa.KosGr
variable {K : Type} [CommRing K] {g : ℕ} {V : ℕ → Type} [∀ j, AddCommGroup (V j)]
  [∀ j, Module K (V j)]

theorem GlobalTheory.KeyKa.KosGr.exact_dd (x : Fin g → ∀ j, V (j + 1) →ₗ[K] V j)
    (hc : ∀ i i' j (y : V (j + 2)), j + 2 ≤ g → x i j (x i' (j + 1) y) = x i' j (x i (j + 1) y))
    (hr : ∀ (i : Fin g) (j : ℕ) (y : V (j + 1)), j + 1 + i ≤ g →
      x i j y ∈ (⨆ (i' : Fin g) (_ : i' < i), LinearMap.range (x i' j)) →
      y ∈ ⨆ (i' : Fin g) (_ : i' < i), LinearMap.range (x i' (j + 1)))
    (r : ℕ) : ∀ (j₀ : ℕ), j₀ + r ≤ g → ∀ c : Finset (Fin g) → ∀ j, V j,
      (∀ I : Finset (Fin g), (∀ k ∈ I, k.val < r) → ∀ j, j = j₀ + I.card → dd x r c I j = 0) →
      ∃ w : Finset (Fin g) → ∀ j, V j, ∀ I : Finset (Fin g), (∀ k ∈ I, k.val < r) → I ≠ ∅ →
        ∀ j, j = j₀ + I.card → c I j = dd x r w I j := by sorry
