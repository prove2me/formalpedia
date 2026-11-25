-- Prove2me | Theorems.Thm_GroundTheory_LocalField_EqualChar_valuation_powerSeriesHom_of_constantCoeff_ne_zero
-- name    : GroundTheory.LocalField.EqualChar.valuation_powerSeriesHom_of_constantCoeff_ne_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:13:33.350435+00:00
-- url     : https://prove2.me/theorems/787e5bc1-ce0a-4b61-a95a-53a1bfb53fb3
-- title:
--   Equal Char: valuation power Series Hom of constant Coeff ne zero
-- statement:
--   The Equal Char construction uses the valuation power Series Hom of constant Coeff ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExamplesLaurent.lean#L163-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExamplesLaurent.lean#L163-L178

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

theorem GroundTheory.LocalField.EqualChar.valuation_powerSeriesHom_of_constantCoeff_ne_zero {F : PowerSeries 𝓀[K]}
    (hF : PowerSeries.constantCoeff F ≠ 0) : valuation K (powerSeriesHom K p F : K) = 1 := by sorry
