-- Prove2me | Theorems.Thm_GlobalTheory_T_preirreducibleSpace_fibreHypersurface_spectrum_iff
-- name    : GlobalTheory.T.preirreducibleSpace_fibreHypersurface_spectrum_iff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:54:47.540048+00:00
-- url     : https://prove2.me/theorems/7a7816ad-619b-412b-8a4f-a35cd7fb12c1
-- title:
--   T: preirreducible Space fibre Hypersurface spectrum iff
-- statement:
--   The T construction uses the preirreducible Space fibre Hypersurface spectrum iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PreirreducibleSpaceFibreHypersurfaceSpectrumIffStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PreirreducibleSpaceFibreHypersurfaceSpectrumIffStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreirreducibleSpaceFibreHypersurfaceSpectrumIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreirreducibleSpaceFibreHypersurfaceSpectrumIffStatement
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

theorem GlobalTheory.T.preirreducibleSpace_fibreHypersurface_spectrum_iff : ∀ (A : Type) [CommRing A] (σ : Type) (f g : MvPolynomial σ A) (k : Type) [Field k] [Algebra A k], PreirreducibleSpace (PrimeSpectrum (k ⊗[A] Localization.Away (Ideal.Quotient.mk (Ideal.span {f}) g))) ↔ IsPreirreducible (PrimeSpectrum.zeroLocus {MvPolynomial.map (algebraMap A k) f} \ PrimeSpectrum.zeroLocus {MvPolynomial.map (algebraMap A k) g}) := by sorry
