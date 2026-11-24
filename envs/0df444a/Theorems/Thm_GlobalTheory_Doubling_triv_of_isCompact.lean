-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_triv_of_isCompact
-- name    : GlobalTheory.Doubling.triv_of_isCompact
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:04.571558+00:00
-- url     : https://prove2.me/theorems/533595ea-9084-499f-97d8-c076c307f5b2
-- title:
--   Doubling: triv of is Compact
-- statement:
--   The Doubling construction uses the triv of is Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L72-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L72-L81

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

theorem GlobalTheory.Doubling.triv_of_isCompact (hP : IsClosed (P : Set G)) (hδ : Continuous δ) (hK : IsCompact (K : Set G)) (p : P)
    (hp : (p : G) ∈ K) : δ p = 1 := by sorry
