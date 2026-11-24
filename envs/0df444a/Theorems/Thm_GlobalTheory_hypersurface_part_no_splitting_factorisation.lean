-- Prove2me | Theorems.Thm_GlobalTheory_hypersurface_part_no_splitting_factorisation
-- name    : GlobalTheory.hypersurface_part_no_splitting_factorisation
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:54:56.991186+00:00
-- url     : https://prove2.me/theorems/a7281ac7-4c0e-4ece-a7d9-07f3da52f5a7
-- title:
--   Global Theory: hypersurface part no splitting factorisation
-- statement:
--   The Global Theory construction uses the hypersurface part no splitting factorisation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NoSplittingFactorisationOfPderivNeZero.lean#L8-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NoSplittingFactorisationOfPderivNeZero.lean#L8-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NoSplittingFactorisationOfPderivNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
open GlobalTheory

theorem GlobalTheory.hypersurface_part_no_splitting_factorisation :
    ∀ (Ω : Type) [Field Ω] (σ : Type) (f g : MvPolynomial σ Ω) (i : σ) (D : ℕ),
      (∀ Q : σ → Ω, MvPolynomial.eval Q f = 0 → MvPolynomial.eval Q g ≠ 0 →
        MvPolynomial.eval Q (MvPolynomial.pderiv i f) ≠ 0) →
      IsPreirreducible (PrimeSpectrum.zeroLocus {f} \ PrimeSpectrum.zeroLocus {g}) →
      ¬ (∃ u v : MvPolynomial σ Ω, u.totalDegree ≤ D ∧ v.totalDegree ≤ D ∧ u * v = f ∧
        ∃ P Q : σ → Ω, MvPolynomial.eval P u = 0 ∧ MvPolynomial.eval P g ≠ 0 ∧
          MvPolynomial.eval Q v = 0 ∧ MvPolynomial.eval Q g ≠ 0) := by sorry
