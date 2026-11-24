-- Prove2me | Theorems.Thm_GlobalTheory_FibreMinimalPrime_trdeg_residueField_eq
-- name    : GlobalTheory.FibreMinimalPrime.trdeg_residueField_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:24:30.706796+00:00
-- url     : https://prove2.me/theorems/19880f2e-5829-4372-96c7-c0507c78f301
-- title:
--   Fibre Minimal Prime: trdeg residue Field eq
-- statement:
--   The Fibre Minimal Prime construction uses the trdeg residue Field eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TrdegResidueFieldEq.lean#L6-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TrdegResidueFieldEq.lean#L6-L77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TrdegResidueFieldEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory GlobalTheory.FibreMinimalPrime

theorem GlobalTheory.FibreMinimalPrime.trdeg_residueField_eq {R : Type} [CommRing R] (r : ℕ) (Q : Ideal (MvPolynomial (Fin r) R)) [Q.IsPrime]
    (hmin : ∀ Q' : Ideal (MvPolynomial (Fin r) R), Q'.IsPrime → Q' ≤ Q →
      Q'.comap (MvPolynomial.C : R →+* _) = Q.comap MvPolynomial.C → Q' = Q) :
    @Algebra.trdeg (Q.comap (MvPolynomial.C : R →+* _)).ResidueField Q.ResidueField _ _
      (Ideal.ResidueField.map (Q.comap MvPolynomial.C) Q MvPolynomial.C rfl).toAlgebra = r := by sorry
