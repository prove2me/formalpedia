-- Prove2me | Theorems.Thm_GroundTheory_LocalField_EqualChar_laurentEquiv_apply
-- name    : GroundTheory.LocalField.EqualChar.laurentEquiv_apply
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:59:21.627846+00:00
-- url     : https://prove2.me/theorems/f9aea4dd-fd88-47fc-a6cf-9d3271a46f96
-- title:
--   Equal Char: laurent Equiv apply
-- statement:
--   The Equal Char construction uses the laurent Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExamplesLaurent.lean#L256-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExamplesLaurent.lean#L256-L256

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

theorem GroundTheory.LocalField.EqualChar.laurentEquiv_apply (x : 𝓀[K]⸨X⸩) : laurentEquiv K p x = laurentHom K p x := by sorry
