-- Prove2me | Theorems.Thm_GroundTheory_LocalField_EqualChar_isEquiv_comap_laurentHom
-- name    : GroundTheory.LocalField.EqualChar.isEquiv_comap_laurentHom
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T01:13:19.085246+00:00
-- url     : https://prove2.me/theorems/2720fc40-23c5-4f9f-a9af-a60a0b2e731e
-- title:
--   Equal Char: is Equiv comap laurent Hom
-- statement:
--   The Equal Char construction uses the is Equiv comap laurent Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExamplesLaurent.lean#L218-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExamplesLaurent.lean#L218-L225

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

theorem GroundTheory.LocalField.EqualChar.isEquiv_comap_laurentHom :
    ((valuation K).comap (laurentHom K p)).IsEquiv (Valued.v : Valuation 𝓀[K]⸨X⸩ ℤᵐ⁰) := by sorry
