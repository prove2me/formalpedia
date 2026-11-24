-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_IsIwasawa_iwAbs_left
-- name    : GlobalTheory.Doubling.IsIwasawa.iwAbs_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:06:38.471695+00:00
-- url     : https://prove2.me/theorems/39121b93-22f2-4473-98b1-4dec1998e8cc
-- title:
--   Is Iwasawa: iw Abs left
-- statement:
--   The Is Iwasawa construction uses the iw Abs left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L53-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L53-L55

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

theorem GlobalTheory.Doubling.IsIwasawa.iwAbs_left (p : P) (g : G) : iwAbs δ K (p * g) = δ p * iwAbs δ K g := by sorry
