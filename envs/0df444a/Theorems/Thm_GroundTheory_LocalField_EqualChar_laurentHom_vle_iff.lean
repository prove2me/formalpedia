-- Prove2me | Theorems.Thm_GroundTheory_LocalField_EqualChar_laurentHom_vle_iff
-- name    : GroundTheory.LocalField.EqualChar.laurentHom_vle_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:13:21.924282+00:00
-- url     : https://prove2.me/theorems/5c976c56-c6f5-4ccb-beb6-9b8a17604308
-- title:
--   Equal Char: laurent Hom vle iff
-- statement:
--   The Equal Char construction uses the laurent Hom vle iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExamplesLaurent.lean#L227-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExamplesLaurent.lean#L227-L231

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

theorem GroundTheory.LocalField.EqualChar.laurentHom_vle_iff (x y : 𝓀[K]⸨X⸩) :
    laurentHom K p x ≤ᵥ laurentHom K p y ↔ x ≤ᵥ y := by sorry
