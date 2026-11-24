-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_continuous_of_prod
-- name    : GlobalTheory.Doubling.continuous_of_prod
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:52:12.76194+00:00
-- url     : https://prove2.me/theorems/29bbd43e-f2cc-4e48-99e0-ba49da5d2d5a
-- title:
--   Doubling: continuous of prod
-- statement:
--   The Doubling construction uses the continuous of prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L87-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L87-L99

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

theorem GlobalTheory.Doubling.continuous_of_prod (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
    (h : ∀ g : G, ∃ p : P, ∃ k ∈ K, g = p * k) {X : Type} [TopologicalSpace X] {f : G → X}
    (hf : Continuous fun x : P × K => f (x.1 * x.2)) : Continuous f := by sorry
