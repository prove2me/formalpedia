-- Prove2me | Theorems.Thm_GlobalTheory_T_unit_prescribed_residue_reduced_finite_algebra
-- name    : GlobalTheory.T.unit_prescribed_residue_reduced_finite_algebra
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:00:34.802284+00:00
-- url     : https://prove2.me/theorems/da5b4b3b-f856-43b6-be04-27477d1eec6a
-- title:
--   T: unit prescribed residue reduced finite algebra
-- statement:
--   The T construction uses the unit prescribed residue reduced finite algebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitPrescribedResidueReducedFiniteAlgebraStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitPrescribedResidueReducedFiniteAlgebraStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitPrescribedResidueReducedFiniteAlgebra
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitPrescribedResidueReducedFiniteAlgebraStatement
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

theorem GlobalTheory.T.unit_prescribed_residue_reduced_finite_algebra : ∀ (K : UQ) (B : InvAlg K), IsReduced B.A → ∀ (m : MaximalSpectrum B.A) (z : B.A ⧸ m.asIdeal), z ≠ 0 → ∃ y : B.Aˣ, Ideal.Quotient.mk m.asIdeal (y : B.A) = z ∧ ∀ m' : MaximalSpectrum B.A, m' ≠ m → Ideal.Quotient.mk m'.asIdeal (y : B.A) = 1 := by sorry
