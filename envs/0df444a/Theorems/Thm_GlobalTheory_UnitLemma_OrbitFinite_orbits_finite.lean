-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_OrbitFinite_orbits_finite
-- name    : GlobalTheory.UnitLemma.OrbitFinite.orbits_finite
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:41:28.382593+00:00
-- url     : https://prove2.me/theorems/b01ba350-8ab7-435e-8648-bba177493269
-- title:
--   Orbit Finite: orbits finite
-- statement:
--   The Orbit Finite construction uses the orbits finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SelfDualStableLatticeUnitOrbitsFinite.lean#L17-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SelfDualStableLatticeUnitOrbitsFinite.lean#L17-L85

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_KappaSumZeroAndStableSumMulZeroOfNotIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsConductorMulMemAdjoinOfSeparableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteSubmodulesBetweenMulLeftImageLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TorusSubmoduleMulLeftImageMemSelfDualStableLattiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RelIndexUnitStabilizerIntegralUnitsNeZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMaximalOrderHullSelfDualStableLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteSelfDualIntegralHermitianLatticesModUnitsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualStableLatticeUnitOrbitsFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.OrbitFinite

theorem GlobalTheory.UnitLemma.OrbitFinite.orbits_finite : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∀ x : B.A, IsUnit x → B.σ x = x → Finite (Orb K.O B.T (B.X x)) ∧ ∀ L ∈ B.X x, stabLat K.O L ⊓ B.T ≤ intUnits K.O B.A ∧ (stabLat K.O L ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) ≠ 0 := by sorry
