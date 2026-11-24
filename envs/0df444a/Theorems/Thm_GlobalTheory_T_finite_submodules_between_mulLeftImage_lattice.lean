-- Prove2me | Theorems.Thm_GlobalTheory_T_finite_submodules_between_mulLeftImage_lattice
-- name    : GlobalTheory.T.finite_submodules_between_mulLeftImage_lattice
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:31:25.894803+00:00
-- url     : https://prove2.me/theorems/81a7eedb-f13e-4adc-9ae4-a26ac6871ac8
-- title:
--   T: finite submodules between mul Left Image lattice
-- statement:
--   The T construction uses the finite submodules between mul Left Image lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteSubmodulesBetweenMulLeftImageLatticeStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteSubmodulesBetweenMulLeftImageLatticeStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteSubmodulesBetweenMulLeftImageLattice
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteSubmodulesBetweenMulLeftImageLatticeStatement
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

theorem GlobalTheory.T.finite_submodules_between_mulLeftImage_lattice : ∀ (K : UQ) (B : InvAlg K) (L : Submodule K.O B.A), IsLat K.O K.E L → ∀ c : K.O, c ≠ 0 → {M : Submodule K.O B.A | mulLat K.O (algebraMap K.O B.A c) L ≤ M ∧ M ≤ L}.Finite := by sorry
