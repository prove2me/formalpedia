-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Orbit_valuation_conj
-- name    : GlobalTheory.UnitLemma.Orbit.valuation_conj
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:28:51.937606+00:00
-- url     : https://prove2.me/theorems/12185381-4ffe-45ab-b934-91737509cf1a
-- title:
--   Orbit: valuation conj
-- statement:
--   The Orbit construction uses the valuation conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocalRingOfIdem.lean#L135-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocalRingOfIdem.lean#L135-L172

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfNotPrimary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit
open GlobalTheory.UnitLemma Polynomial IsLocalRing ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion
variable {K : UQ}

theorem GlobalTheory.UnitLemma.Orbit.valuation_conj (x : K.E) : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E (K.c x) =
    (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E x := by sorry
