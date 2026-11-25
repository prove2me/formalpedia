-- Prove2me | Theorems.Thm_GlobalTheory_GramCount_norm_gauss_sum_ip_le
-- name    : GlobalTheory.GramCount.norm_gauss_sum_ip_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:28:01.659199+00:00
-- url     : https://prove2.me/theorems/86e44af6-e4c4-4e8e-9e9c-9e96c4ab31c1
-- title:
--   Gram Count: norm gauss sum ip le
-- statement:
--   The Gram Count construction uses the norm gauss sum ip le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormGaussSumHermitianFormLinearLe.lean#L42-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormGaussSumHermitianFormLinearLe.lean#L42-L78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormGaussSumHermitianFormLinearLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.GramCount
open scoped Classical
open GlobalTheory GlobalTheory.GramCount

theorem GlobalTheory.GramCount.norm_gauss_sum_ip_le {B : Type} [CommRing B] [Fintype B] (c : B →+* B)
    (hc : ∀ u, c (c u) = u) (q : ℕ) (_hq : 2 ≤ q) (hB : Fintype.card B = q ^ 2)
    (χ : AddChar B ℂ) (hχ : χ.IsPrimitive) (hinv : ∀ u, χ (c u) = χ u) (n : ℕ) (a : B)
    (ha : IsUnit (a + c a)) (v : Fin n → B) :
    ‖∑ y : Fin n → B, χ (a * ip c y y + ip c y v)‖ ≤ (q : ℝ) ^ n := by sorry
