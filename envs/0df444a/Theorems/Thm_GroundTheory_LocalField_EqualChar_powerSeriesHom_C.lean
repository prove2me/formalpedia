-- Prove2me | Theorems.Thm_GroundTheory_LocalField_EqualChar_powerSeriesHom_C
-- name    : GroundTheory.LocalField.EqualChar.powerSeriesHom_C
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:13:33.675865+00:00
-- url     : https://prove2.me/theorems/8fdd45e7-2f37-4804-aad3-9845d03ddf2a
-- title:
--   Equal Char: power Series Hom C
-- statement:
--   The Equal Char construction uses the power Series Hom C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExamplesLaurent.lean#L108-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExamplesLaurent.lean#L108-L110

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
attribute [local instance] GroundTheory.LocalField.EqualChar.uniformSpaceK
attribute [local instance] GroundTheory.LocalField.EqualChar.isUniformAddGroupK
attribute [local instance] GroundTheory.LocalField.EqualChar.uniformSpaceResidue
attribute [local instance] GroundTheory.LocalField.EqualChar.discreteUniformityResidue

theorem GroundTheory.LocalField.EqualChar.powerSeriesHom_C (a : 𝓀[K]) :
    powerSeriesHom K p (PowerSeries.C a) = teichmullerHom K p a := by sorry
