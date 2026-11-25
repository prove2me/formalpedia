-- Prove2me | Theorems.Thm_GroundTheory_LocalField_EqualChar_valuation_teichmullerHom
-- name    : GroundTheory.LocalField.EqualChar.valuation_teichmullerHom
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:13:34.385165+00:00
-- url     : https://prove2.me/theorems/7b9e83aa-c98d-44c8-b587-69dcc33ddcde
-- title:
--   Equal Char: valuation teichmuller Hom
-- statement:
--   The Equal Char construction uses the valuation teichmuller Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExamplesLaurent.lean#L85-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExamplesLaurent.lean#L85-L88

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

theorem GroundTheory.LocalField.EqualChar.valuation_teichmullerHom {a : 𝓀[K]} (ha : a ≠ 0) :
    valuation K (teichmullerHom K p a : K) = 1 := by sorry
