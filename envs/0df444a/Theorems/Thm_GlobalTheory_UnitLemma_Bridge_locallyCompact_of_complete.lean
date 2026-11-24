-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Bridge_locallyCompact_of_complete
-- name    : GlobalTheory.UnitLemma.Bridge.locallyCompact_of_complete
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:26:19.79483+00:00
-- url     : https://prove2.me/theorems/0b8e8870-352e-4bd0-b395-4f3081a92ebe
-- title:
--   Bridge: locally Compact of complete
-- statement:
--   The Bridge construction uses the locally Compact of complete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LocallyCompactOfComplete.lean#L86-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LocallyCompactOfComplete.lean#L86-L147

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LocallyCompactOfComplete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Bridge

theorem GlobalTheory.UnitLemma.Bridge.locallyCompact_of_complete {O E : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    [NormedField E] [Algebra O E] (hinj : Function.Injective (algebraMap O E))
    (hball : ∀ y : E, ‖y‖ ≤ 1 ↔ y ∈ (algebraMap O E).range) : LocallyCompactSpace E := by sorry
