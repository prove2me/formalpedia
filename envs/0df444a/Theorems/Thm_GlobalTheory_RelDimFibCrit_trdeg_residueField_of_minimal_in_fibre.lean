-- Prove2me | Theorems.Thm_GlobalTheory_RelDimFibCrit_trdeg_residueField_of_minimal_in_fibre
-- name    : GlobalTheory.RelDimFibCrit.trdeg_residueField_of_minimal_in_fibre
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:21:45.248554+00:00
-- url     : https://prove2.me/theorems/099c3da0-76d7-42c8-a281-3ba9a3806a04
-- title:
--   Rel Dim Fib Crit: trdeg residue Field of minimal in fibre
-- statement:
--   The Rel Dim Fib Crit construction uses the trdeg residue Field of minimal in fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/SmoothRelativeDimOfTrdeg.lean#L10-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/SmoothRelativeDimOfTrdeg.lean#L10-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TrdegResidueFieldEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ResidueFieldIsAlgebraicOfEtale
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ResidueFieldIsoInvCompSpec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_SmoothRelativeDimOfTrdeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory GlobalTheory.RelDimFibCrit

theorem GlobalTheory.RelDimFibCrit.trdeg_residueField_of_minimal_in_fibre {R B : Type} [CommRing R] [CommRing B] (φ : R →+* B) (r : ℕ)
    (hφ : φ.IsStandardSmoothOfRelativeDimension r) (P : Ideal B) [P.IsPrime]
    (hP : ∀ P' : Ideal B, P'.IsPrime → P' ≤ P → P'.comap φ = P.comap φ → P' = P) :
    @Algebra.trdeg (P.comap φ).ResidueField P.ResidueField _ _
      (Ideal.ResidueField.map (P.comap φ) P φ rfl).toAlgebra = r := by sorry
