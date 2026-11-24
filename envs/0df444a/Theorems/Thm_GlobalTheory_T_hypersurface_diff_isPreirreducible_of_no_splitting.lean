-- Prove2me | Theorems.Thm_GlobalTheory_T_hypersurface_diff_isPreirreducible_of_no_splitting
-- name    : GlobalTheory.T.hypersurface_diff_isPreirreducible_of_no_splitting
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:46:31.045646+00:00
-- url     : https://prove2.me/theorems/c076bd4d-fd5b-41fd-a968-710ead1f0f64
-- title:
--   T: hypersurface diff is Preirreducible of no splitting
-- statement:
--   The T construction uses the hypersurface diff is Preirreducible of no splitting property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HypersurfaceDiffIsPreirreducibleOfNoSplittingStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HypersurfaceDiffIsPreirreducibleOfNoSplittingStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HypersurfaceDiffIsPreirreducibleOfNoSplitting
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HypersurfaceDiffIsPreirreducibleOfNoSplittingStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.hypersurface_diff_isPreirreducible_of_no_splitting : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (σ : Type) [Finite σ] (f g : MvPolynomial σ Ω) (D : ℕ), f ≠ 0 → f.totalDegree ≤ D → ¬ (∃ u v : MvPolynomial σ Ω, u.totalDegree ≤ D ∧ v.totalDegree ≤ D ∧ u * v = f ∧ ∃ P Q : σ → Ω, MvPolynomial.eval P u = 0 ∧ MvPolynomial.eval P g ≠ 0 ∧ MvPolynomial.eval Q v = 0 ∧ MvPolynomial.eval Q g ≠ 0) → IsPreirreducible (PrimeSpectrum.zeroLocus {f} \ PrimeSpectrum.zeroLocus {g}) := by sorry
