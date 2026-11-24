-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_IsIwasawa_continuous_iwAbs
-- name    : GlobalTheory.Doubling.IsIwasawa.continuous_iwAbs
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:03:46.006806+00:00
-- url     : https://prove2.me/theorems/e6752e9b-6243-4f38-ae5b-d3b5d47d8c5c
-- title:
--   Is Iwasawa: continuous iw Abs
-- statement:
--   The Is Iwasawa construction uses the continuous iw Abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L101-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L101-L103

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

theorem GlobalTheory.Doubling.IsIwasawa.continuous_iwAbs (h : IsIwasawa δ K) (hP : IsClosed (P : Set G)) (hδ : Continuous δ)
    (hK : IsCompact (K : Set G)) : Continuous (iwAbs δ K) := by sorry
