-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_IsIwasawa_eq_iwAbs
-- name    : GlobalTheory.Doubling.IsIwasawa.eq_iwAbs
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:07:21.008641+00:00
-- url     : https://prove2.me/theorems/edab458d-99d2-5db6-b791-b3dd8814291f
-- title:
--   Is Iwasawa: eq iw Abs
-- statement:
--   The Is Iwasawa construction uses the eq iw Abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L61-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L61-L64

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Doubling
open scoped NNReal
open MeasureTheory
variable {G : Type} [Group G] {P : Subgroup G} (δ : P →* ℝ≥0) (K : Subgroup G)
variable {δ K}
open GlobalTheory.Doubling.IsIwasawa
variable (h : IsIwasawa δ K)
include h

theorem GlobalTheory.Doubling.IsIwasawa.eq_iwAbs {f : G → ℝ≥0} (h1 : f 1 = 1) (hl : ∀ (p : P) g, f (p * g) = δ p * f g)
    (hr : ∀ g, ∀ k ∈ K, f (g * k) = f g) : f = iwAbs δ K := by sorry
