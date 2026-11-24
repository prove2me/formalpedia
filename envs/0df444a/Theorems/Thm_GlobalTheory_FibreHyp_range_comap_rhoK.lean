-- Prove2me | Theorems.Thm_GlobalTheory_FibreHyp_range_comap_rhoK
-- name    : GlobalTheory.FibreHyp.range_comap_rhoK
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:24:54.3302+00:00
-- url     : https://prove2.me/theorems/6ef5bdb6-1934-4fee-8873-4b141289da8b
-- title:
--   Fibre Hyp: range comap rho K
-- statement:
--   The Fibre Hyp construction uses the range comap rho K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PreirreducibleSpaceFibreHypersurfaceSpectrumIff.lean#L128-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PreirreducibleSpaceFibreHypersurfaceSpectrumIff.lean#L128-L162

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreirreducibleSpaceFibreHypersurfaceSpectrumIff
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
noncomputable section
open GlobalTheory GlobalTheory.FibreHyp
variable {A : Type} [CommRing A] {σ : Type} (f g : MvPolynomial σ A) (k : Type) [Field k] [Algebra A k]

theorem GlobalTheory.FibreHyp.range_comap_rhoK : Set.range (PrimeSpectrum.comap (rhoK f g k).toRingHom) =
    PrimeSpectrum.zeroLocus {MvPolynomial.map (algebraMap A k) f} \
      PrimeSpectrum.zeroLocus {MvPolynomial.map (algebraMap A k) g} := by sorry
