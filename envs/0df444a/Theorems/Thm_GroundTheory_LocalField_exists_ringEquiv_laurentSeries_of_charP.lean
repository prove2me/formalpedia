-- Prove2me | Theorems.Thm_GroundTheory_LocalField_exists_ringEquiv_laurentSeries_of_charP
-- name    : GroundTheory.LocalField.exists_ringEquiv_laurentSeries_of_charP
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:00:08.767059+00:00
-- url     : https://prove2.me/theorems/c7396101-8225-5f21-8662-6a7539aa6220
-- title:
--   Local Field: exists ring Equiv laurent Series of char P
-- statement:
--   The Local Field construction uses the exists ring Equiv laurent Series of char P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExamplesLaurent.lean#L260-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExamplesLaurent.lean#L260-L269

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

theorem GroundTheory.LocalField.exists_ringEquiv_laurentSeries_of_charP (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (p : ℕ) [Fact p.Prime] [CharP K p] :
    ∃ e : K ≃+* 𝓀[K]⸨X⸩, (∀ x y, e x ≤ᵥ e y ↔ x ≤ᵥ y) ∧ Continuous e ∧ Continuous e.symm := by sorry
