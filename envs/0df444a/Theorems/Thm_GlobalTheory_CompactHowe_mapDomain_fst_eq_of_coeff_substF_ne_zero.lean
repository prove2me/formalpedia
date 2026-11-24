-- Prove2me | Theorems.Thm_GlobalTheory_CompactHowe_mapDomain_fst_eq_of_coeff_substF_ne_zero
-- name    : GlobalTheory.CompactHowe.mapDomain_fst_eq_of_coeff_substF_ne_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:49:16.275789+00:00
-- url     : https://prove2.me/theorems/16f5ef74-784a-4dac-87be-203154ac9acf
-- title:
--   Compact Howe: map Domain fst eq of coeff subst F ne zero
-- statement:
--   The Compact Howe construction uses the map Domain fst eq of coeff subst F ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MapDomainFstEqOfCoeffMatrixFamilyBilateralSubsti.lean#L27-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MapDomainFstEqOfCoeffMatrixFamilyBilateralSubsti.lean#L27-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TotalDegreeSubstFLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MapDomainFstEqOfCoeffMatrixFamilyBilateralSubsti
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open GlobalTheory GlobalTheory.CompactHowe

theorem GlobalTheory.CompactHowe.mapDomain_fst_eq_of_coeff_substF_ne_zero {ι : Type} {N n : ℕ} (h : ι → Matrix (Fin N) (Fin N) ℂ)
    (g : ι → Matrix (Fin n) (Fin n) ℂ) (k k' : ι × Fin N × Fin n →₀ ℕ)
    (hk : MvPolynomial.coeff k' (substF h g (MvPolynomial.monomial k 1)) ≠ 0) :
    Finsupp.mapDomain Prod.fst k' = Finsupp.mapDomain Prod.fst k := by sorry
