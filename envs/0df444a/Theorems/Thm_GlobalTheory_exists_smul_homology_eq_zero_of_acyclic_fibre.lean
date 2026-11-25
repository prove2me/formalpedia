-- Prove2me | Theorems.Thm_GlobalTheory_exists_smul_homology_eq_zero_of_acyclic_fibre
-- name    : GlobalTheory.exists_smul_homology_eq_zero_of_acyclic_fibre
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T15:05:37.143563+00:00
-- url     : https://prove2.me/theorems/f0809f7d-ed5e-43c7-a82c-e5d080bc1f9c
-- title:
--   Global Theory: exists smul homology eq zero of acyclic fibre
-- statement:
--   The Global Theory construction uses the exists smul homology eq zero of acyclic fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsSmulHomologyEqZeroOfAcyclicFibre.lean#L50-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsSmulHomologyEqZeroOfAcyclicFibre.lean#L50-L90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndKerBaseChangeOfForallResidueField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsSmulHomologyEqZeroOfAcyclicFibre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits TensorProduct Function
open GlobalTheory
set_option backward.isDefEq.respectTransparency false

theorem GlobalTheory.exists_smul_homology_eq_zero_of_acyclic_fibre (R : Type) [CommRing R] [IsNoetherianRing R]
    (K : Type) [Field K] (χ : R →+* K) (C : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ)
    (hn : ∀ p, n < p → IsZero (C.X p)) (hflat : ∀ p, Module.Flat R (C.X p))
    (hfin : ∀ p, Module.Finite R (C.homology p))
    (hac : (((ModuleCat.extendScalars.{0, 0, 0} χ).mapHomologicalComplex _).obj C).Acyclic)
    (p : ℕ) : ∃ r : R, χ r ≠ 0 ∧ ∀ z : C.homology p, r • z = 0 := by sorry
