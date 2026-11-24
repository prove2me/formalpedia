-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_isIwasawa_of_isCompact
-- name    : GlobalTheory.Doubling.isIwasawa_of_isCompact
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:51:35.966804+00:00
-- url     : https://prove2.me/theorems/668cf68c-49a5-4034-a1bd-70fe24cceabd
-- title:
--   Doubling: is Iwasawa of is Compact
-- statement:
--   The Doubling construction uses the is Iwasawa of is Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L84-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L84-L85

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
variable [TopologicalSpace G] [IsTopologicalGroup G]
omit [IsTopologicalGroup G]

theorem GlobalTheory.Doubling.isIwasawa_of_isCompact (hP : IsClosed (P : Set G)) (hδ : Continuous δ) (hK : IsCompact (K : Set G))
    (h : ∀ g : G, ∃ p : P, ∃ k ∈ K, g = p * k) : IsIwasawa δ K := by sorry
