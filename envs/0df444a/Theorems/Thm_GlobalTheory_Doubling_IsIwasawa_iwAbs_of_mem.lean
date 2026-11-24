-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_IsIwasawa_iwAbs_of_mem
-- name    : GlobalTheory.Doubling.IsIwasawa.iwAbs_of_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:33:21.904053+00:00
-- url     : https://prove2.me/theorems/02879341-2614-4b5c-aec2-4a777a8d7be5
-- title:
--   Is Iwasawa: iw Abs of mem
-- statement:
--   The Is Iwasawa construction uses the iw Abs of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L51-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L51-L51

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

theorem GlobalTheory.Doubling.IsIwasawa.iwAbs_of_mem {k : G} (hk : k ∈ K) : iwAbs δ K k = 1 := by sorry
