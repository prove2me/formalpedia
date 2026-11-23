-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_IsIwasawa_iwAbs_mul
-- name    : GlobalTheory.Doubling.IsIwasawa.iwAbs_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:58:08.070886+00:00
-- url     : https://prove2.me/theorems/8a47c86c-4676-4c57-855c-60cd3ab7f3cb
-- title:
--   Is Iwasawa: iw Abs mul
-- statement:
--   The Is Iwasawa construction uses the iw Abs mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L47-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L47-L47

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

theorem GlobalTheory.Doubling.IsIwasawa.iwAbs_mul (p : P) {k : G} (hk : k ∈ K) : iwAbs δ K (p * k) = δ p := by sorry
