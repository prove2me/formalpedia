-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_finite_orbits_stLat_of_separable
-- name    : GlobalTheory.UnitLemma.finite_orbits_stLat_of_separable
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:09:30.890799+00:00
-- url     : https://prove2.me/theorems/beb20ee8-eb6f-4510-a4d7-d0950bb75229
-- title:
--   Unit Lemma: finite orbits st Lat of separable
-- statement:
--   The Unit Lemma construction uses the finite orbits st Lat of separable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteUnitOrbitsStableLatticesSeparable.lean#L24-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteUnitOrbitsStableLatticesSeparable.lean#L24-L90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ComapInlMemStLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegralClosureFgDvrOfSeparableCharpolyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqSubmoduleMulLeftImageIntegralClosureOfSeparablStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAevalEqOfMulLeftCharpolySeparableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCommonDenominatorAevalOfFgStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteSubmodulesBetweenSmulAndSelfStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteUnitOrbitsStableLatticesSeparable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.UnitLemma

theorem GlobalTheory.UnitLemma.finite_orbits_stLat_of_separable : ∀ (O E A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A] [IsScalarTower O E A] [Module.Finite E A] (g : A), (LinearMap.mulLeft E g).charpoly.Separable → Finite (MulAction.orbitRel.Quotient Aˣ (stLat O E g)) := by sorry
