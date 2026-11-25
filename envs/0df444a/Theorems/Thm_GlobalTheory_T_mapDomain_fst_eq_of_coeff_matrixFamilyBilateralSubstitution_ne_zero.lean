-- Prove2me | Theorems.Thm_GlobalTheory_T_mapDomain_fst_eq_of_coeff_matrixFamilyBilateralSubstitution_ne_zero
-- name    : GlobalTheory.T.mapDomain_fst_eq_of_coeff_matrixFamilyBilateralSubstitution_ne_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:35:10.703423+00:00
-- url     : https://prove2.me/theorems/4612866d-6311-416d-b32d-2f8ab5c4bff9
-- title:
--   T: map Domain fst eq of coeff matrix Family Bilateral Substitution ne zero
-- statement:
--   The T construction uses the map Domain fst eq of coeff matrix Family Bilateral Substitution ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MapDomainFstEqOfCoeffMatrixFamilyBilateralSubstiStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MapDomainFstEqOfCoeffMatrixFamilyBilateralSubstiStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MapDomainFstEqOfCoeffMatrixFamilyBilateralSubsti
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TotalDegreeSubstFLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MapDomainFstEqOfCoeffMatrixFamilyBilateralSubstiStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.mapDomain_fst_eq_of_coeff_matrixFamilyBilateralSubstitution_ne_zero : ∀ {ι : Type} {N n : ℕ} (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ) (k k' : ι × Fin N × Fin n →₀ ℕ), MvPolynomial.coeff k' (GlobalTheory.CompactHowe.substF h g (MvPolynomial.monomial k 1)) ≠ 0 → Finsupp.mapDomain Prod.fst k' = Finsupp.mapDomain Prod.fst k := by sorry
