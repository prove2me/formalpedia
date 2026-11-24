-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Orbit_val_conj_le
-- name    : GlobalTheory.UnitLemma.Orbit.val_conj_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:28:21.00624+00:00
-- url     : https://prove2.me/theorems/bd069633-d459-497b-85db-87624b3d7104
-- title:
--   Orbit: val conj le
-- statement:
--   The Orbit construction uses the val conj le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocalRingOfIdem.lean#L128-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocalRingOfIdem.lean#L128-L133

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

theorem GlobalTheory.UnitLemma.Orbit.val_conj_le (x : K.E) (h : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E x ≤ 1) :
    (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E (K.c x) ≤ 1 := by sorry
