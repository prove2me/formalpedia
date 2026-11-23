-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Orbit_charpoly_dvd_map_of_aeval_eq_zero
-- name    : GlobalTheory.UnitLemma.Orbit.charpoly_dvd_map_of_aeval_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:40:27.048954+00:00
-- url     : https://prove2.me/theorems/44f3e199-b6c1-41a7-8d1e-78c2193ad12d
-- title:
--   Orbit: charpoly dvd map of aeval eq zero
-- statement:
--   The Orbit construction uses the charpoly dvd map of aeval eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocalRingOfIdem.lean#L78-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocalRingOfIdem.lean#L78-L93

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

theorem GlobalTheory.UnitLemma.Orbit.charpoly_dvd_map_of_aeval_eq_zero (B : InvAlg K) (hs : B.P.Separable) (f : K.O[X]) (hf : aeval B.g f = 0) :
    B.P ∣ f.map (algebraMap K.O K.E) := by sorry
