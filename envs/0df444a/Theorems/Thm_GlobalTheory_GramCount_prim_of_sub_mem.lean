-- Prove2me | Theorems.Thm_GlobalTheory_GramCount_prim_of_sub_mem
-- name    : GlobalTheory.GramCount.prim_of_sub_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:56:05.64164+00:00
-- url     : https://prove2.me/theorems/4ae8656a-da80-4b7e-9e52-c905cd1da214
-- title:
--   Gram Count: prim of sub mem
-- statement:
--   The Gram Count construction uses the prim of sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PrimOfIsUnitDet.lean#L87-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PrimOfIsUnitDet.lean#L87-L102

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.GramCount
variable {A : Type} [CommRing A]
variable (c : A →+* A) {n : ℕ}

theorem GlobalTheory.GramCount.prim_of_sub_mem (hc : ∀ u, c (c u) = u) (I : Ideal A) (hI : ∀ u ∈ I, IsUnit (1 + u))
    {m : ℕ} (x y : Fin m → Fin n → A)
    (h : ∀ a b, ip c (x a) (y b) - (if a = b then 1 else 0) ∈ I) : Prim c x := by sorry
