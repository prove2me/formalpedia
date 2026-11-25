-- Prove2me | Theorems.Thm_GlobalTheory_GramCount_hensel_iter
-- name    : GlobalTheory.GramCount.hensel_iter
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:29:00.856444+00:00
-- url     : https://prove2.me/theorems/0ae91206-ac44-5e5f-951e-7112f6b0d927
-- title:
--   Gram Count: hensel iter
-- statement:
--   The Gram Count construction uses the hensel iter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PrimitiveTuplesWithGramMatrixHenselCount.lean#L93-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PrimitiveTuplesWithGramMatrixHenselCount.lean#L93-L109

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HenselStepCardComap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimitiveTuplesWithGramMatrixHenselCount
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
variable {A : Type} [CommRing A]

theorem GlobalTheory.GramCount.hensel_iter [Finite A] (c : A →+* A) (hc : ∀ u, c (c u) = u) {ω : A}
    (hω : IsUnit (ω - c ω)) {p : A} (hp : c p = p) (hn : IsNilpotent p) (m n : ℕ)
    (G : Matrix (Fin m) (Fin m) A) (k : ℕ) :
    Set.ncard {x : Fin m → Fin n → A | x ∈ {x | Prim c x} ∧
        henselGram c x - G ∈ henselHerm c m (p ^ (0 + 1))} *
      Nat.card (henselHerm c m (p ^ (k + 1))) =
    Set.ncard {x : Fin m → Fin n → A | x ∈ {x | Prim c x} ∧
        henselGram c x - G ∈ henselHerm c m (p ^ (k + 1))} *
      Nat.card (henselHerm c m (p ^ (0 + 1))) := by sorry
