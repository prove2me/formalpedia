-- Prove2me | Theorems.Thm_GlobalTheory_GramCount_hensel_step
-- name    : GlobalTheory.GramCount.hensel_step
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:29:05.571808+00:00
-- url     : https://prove2.me/theorems/2e93bf96-94d0-5447-9ea4-04236bfca1b0
-- title:
--   Gram Count: hensel step
-- statement:
--   The Gram Count construction uses the hensel step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PrimitiveTuplesWithGramMatrixHenselCount.lean#L36-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PrimitiveTuplesWithGramMatrixHenselCount.lean#L36-L91

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

theorem GlobalTheory.GramCount.hensel_step [Finite A] (c : A →+* A) (hc : ∀ u, c (c u) = u) {ω : A}
    (hω : IsUnit (ω - c ω)) {p : A} (hp : c p = p) (hn : IsNilpotent p) (m n : ℕ)
    (G : Matrix (Fin m) (Fin m) A) (i : ℕ) :
    Set.ncard {x : Fin m → Fin n → A | x ∈ {x | Prim c x} ∧
        henselGram c x - G ∈ henselHerm c m (p ^ (i + 1))} *
      Nat.card (henselHerm c m (p ^ (i + 2))) =
    Set.ncard {x : Fin m → Fin n → A | x ∈ {x | Prim c x} ∧
        henselGram c x - G ∈ henselHerm c m (p ^ (i + 2))} *
      Nat.card (henselHerm c m (p ^ (i + 1))) := by sorry
