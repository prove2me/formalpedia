-- Prove2me | Theorems.Thm_GlobalTheory_NormOneSplit_card_norm_classes
-- name    : GlobalTheory.NormOneSplit.card_norm_classes
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:37:43.669778+00:00
-- url     : https://prove2.me/theorems/5a233bc7-426f-4459-be52-f90f4a92fb3f
-- title:
--   Norm One Split: card norm classes
-- statement:
--   The Norm One Split construction uses the card norm classes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsForallHomEq.lean#L223-L294
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsForallHomEq.lean#L223-L294

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsForallHomEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal
open GlobalTheory GlobalTheory.NormOneSplit
open NumberField Module Matrix
open scoped ENNReal

theorem GlobalTheory.NormOneSplit.card_norm_classes : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E], _root_.Formalism.BasicNotions.CMData F E → ∀ T : ℕ, T.Prime → (∀ P : Ideal (𝓞 E), P.IsMaximal → ((T : 𝓞 E) ∈ P) → Ideal.absNorm P = T ∧ (T : 𝓞 E) ∉ P ^ 2) → ∀ c : 𝓞 E, star (c : E) = (c : E) → IsCoprime c (T : 𝓞 E) → Nat.card {a : 𝓞 E ⧸ Ideal.span {(T : 𝓞 E)} // ∃ x y : 𝓞 E, Ideal.Quotient.mk _ x = a ∧ (y : E) = star (x : E) ∧ x * y - c ∈ Ideal.span {(T : 𝓞 E)}} = (T - 1) ^ finrank ℚ F := by sorry
