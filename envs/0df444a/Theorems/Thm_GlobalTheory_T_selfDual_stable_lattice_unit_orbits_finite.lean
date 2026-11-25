-- Prove2me | Theorems.Thm_GlobalTheory_T_selfDual_stable_lattice_unit_orbits_finite
-- name    : GlobalTheory.T.selfDual_stable_lattice_unit_orbits_finite
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:48:45.855795+00:00
-- url     : https://prove2.me/theorems/33a3c47c-61ec-423a-8bb4-f0079de44a0b
-- title:
--   T: self Dual stable lattice unit orbits finite
-- statement:
--   The T construction uses the self Dual stable lattice unit orbits finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SelfDualStableLatticeUnitOrbitsFiniteStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SelfDualStableLatticeUnitOrbitsFiniteStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualStableLatticeUnitOrbitsFinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualStableLatticeUnitOrbitsFiniteStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.selfDual_stable_lattice_unit_orbits_finite : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∀ x : B.A, IsUnit x → B.σ x = x → Finite (Orb K.O B.T (B.X x)) ∧ ∀ L ∈ B.X x, stabLat K.O L ⊓ B.T ≤ intUnits K.O B.A ∧ (stabLat K.O L ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) ≠ 0 := by sorry
