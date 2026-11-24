-- Prove2me | Theorems.Thm_GlobalTheory_KeyKa_KosGr_exists_sum_of_mem_iSup
-- name    : GlobalTheory.KeyKa.KosGr.exists_sum_of_mem_iSup
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:47:14.662857+00:00
-- url     : https://prove2.me/theorems/a4dd8fbc-b9fa-4394-9dbe-9ff61b0115e5
-- title:
--   Kos Gr: exists sum of mem i Sup
-- statement:
--   The Kos Gr construction uses the exists sum of mem i Sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/KoszulExactOfGradedRegular.lean#L65-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/KoszulExactOfGradedRegular.lean#L65-L90

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

theorem GlobalTheory.KeyKa.KosGr.exists_sum_of_mem_iSup {A B : Type} [AddCommGroup A] [AddCommGroup B] [Module K A]
    [Module K B] (f : Fin g → A →ₗ[K] B) (t : Fin g) (y : B)
    (hy : y ∈ ⨆ (i : Fin g) (_ : i < t), LinearMap.range (f i)) :
    ∃ z : Fin g → A, y = ∑ i : Fin g, if i.val < t.val then f i (z i) else 0 := by sorry
