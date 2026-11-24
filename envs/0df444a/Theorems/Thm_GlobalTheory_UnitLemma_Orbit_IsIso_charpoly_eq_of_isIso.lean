-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Orbit_IsIso_charpoly_eq_of_isIso
-- name    : GlobalTheory.UnitLemma.Orbit.IsIso.charpoly_eq_of_isIso
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T16:47:48.357701+00:00
-- url     : https://prove2.me/theorems/451cb296-d22f-4c19-87b6-7374871b97e3
-- title:
--   Is Iso: charpoly eq of is Iso
-- statement:
--   The Is Iso construction uses the charpoly eq of is Iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocalRingOfIdem.lean#L306-L311
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocalRingOfIdem.lean#L306-L311

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
open GlobalTheory.UnitLemma.Orbit.IsIso
variable {B C : InvAlg K} {φ : B.A ≃ₐ[K.E] C.A}

theorem GlobalTheory.UnitLemma.Orbit.IsIso.charpoly_eq_of_isIso (h : IsIso φ) : C.P = B.P := by sorry
