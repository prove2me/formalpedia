-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_iwAbs_mul_of_triv
-- name    : GlobalTheory.Doubling.iwAbs_mul_of_triv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:06.930664+00:00
-- url     : https://prove2.me/theorems/c7480968-d022-44c9-8cde-131c2154f1e1
-- title:
--   Doubling: iw Abs mul of triv
-- statement:
--   The Doubling construction uses the iw Abs mul of triv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L31-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L31-L40

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

theorem GlobalTheory.Doubling.iwAbs_mul_of_triv (h : ∀ p : P, (p : G) ∈ K → δ p = 1) (p : P) {k : G} (hk : k ∈ K) :
    iwAbs δ K (p * k) = δ p := by sorry
