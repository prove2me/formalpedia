-- Prove2me | Theorems.Thm_GlobalTheory_GramCount_hensel_count
-- name    : GlobalTheory.GramCount.hensel_count
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:28:54.515527+00:00
-- url     : https://prove2.me/theorems/4cd46651-6427-538a-b8d1-6701755ef7be
-- title:
--   Gram Count: hensel count
-- statement:
--   The Gram Count construction uses the hensel count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PrimitiveTuplesWithGramMatrixHenselCount.lean#L111-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PrimitiveTuplesWithGramMatrixHenselCount.lean#L111-L136

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

theorem GlobalTheory.GramCount.hensel_count : ∀ {A : Type} [CommRing A] [Finite A] (c : A →+* A), (∀ u, c (c u) = u) → ∀ (ω : A), IsUnit (ω - c ω) → ∀ (p : A), c p = p → IsNilpotent p → ∀ (m n : ℕ) (G : Matrix (Fin m) (Fin m) A), (∀ a b, c (G b a) = G a b) → Set.ncard (sols c n G) * Nat.card {H : Matrix (Fin m) (Fin m) A // (∀ a b, c (H b a) = H a b) ∧ ∀ a b, p ∣ H a b} = Set.ncard {x : Fin m → Fin n → A | Prim c x ∧ ∀ a b, p ∣ ip c (x b) (x a) - G a b} := by sorry
