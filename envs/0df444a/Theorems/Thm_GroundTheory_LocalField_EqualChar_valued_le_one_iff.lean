-- Prove2me | Theorems.Thm_GroundTheory_LocalField_EqualChar_valued_le_one_iff
-- name    : GroundTheory.LocalField.EqualChar.valued_le_one_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:13:16.860541+00:00
-- url     : https://prove2.me/theorems/b594e28b-75ae-413c-baf9-a24b990eda34
-- title:
--   Equal Char: valued le one iff
-- statement:
--   The Equal Char construction uses the valued le one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExamplesLaurent.lean#L207-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExamplesLaurent.lean#L207-L216

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Examples
import Definitions.Def_GroundTheory_LocalFields_ExamplesTeichmuller
import Definitions.Def_GroundTheory_LocalFields_ExamplesLaurent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open scoped LaurentSeries
open GroundTheory GroundTheory.LocalField
open ValuativeRel Polynomial IsLocalRing Topology Filter WithZero HahnSeries
open GroundTheory.LocalField.EqualChar
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (p : ℕ) [Fact p.Prime] [CharP K p]
omit [Fact p.Prime] [CharP K p]

theorem GroundTheory.LocalField.EqualChar.valued_le_one_iff {x : 𝓀[K]⸨X⸩} (hx : x ≠ 0) : Valued.v x ≤ 1 ↔ 0 ≤ x.order := by sorry
