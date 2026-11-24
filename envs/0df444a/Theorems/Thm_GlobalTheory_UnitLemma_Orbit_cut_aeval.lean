-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Orbit_cut_aeval
-- name    : GlobalTheory.UnitLemma.Orbit.cut_aeval
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:29:10.175065+00:00
-- url     : https://prove2.me/theorems/0d645992-0006-42fa-8105-8d584cebd6c1
-- title:
--   Orbit: cut aeval
-- statement:
--   The Orbit construction uses the cut aeval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocalRingOfIdem.lean#L399-L401
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocalRingOfIdem.lean#L399-L401

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

theorem GlobalTheory.UnitLemma.Orbit.cut_aeval (B : InvAlg K) (e : B.A) (he : B.σ e = e) (f : K.O[X]) :
    aeval (cut B e he).g f = Ideal.Quotient.mk (Ideal.span {e}) (aeval B.g f) := by sorry
