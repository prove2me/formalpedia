-- Prove2me | Theorems.Thm_GlobalTheory_T_fourier_inversion_invariant_matrix
-- name    : GlobalTheory.T.fourier_inversion_invariant_matrix
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:32:09.620884+00:00
-- url     : https://prove2.me/theorems/f7487292-08ba-4c25-b50b-45ea719d8114
-- title:
--   T: fourier inversion invariant matrix
-- statement:
--   The T construction uses the fourier inversion invariant matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierInversionInvariantMatrixStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierInversionInvariantMatrixStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierInversionInvariantMatrix
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierInversionInvariantMatrixStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.fourier_inversion_invariant_matrix : ∀ (A : Type) [CommRing A] [MeasurableSpace A] (ν : Measure A) [SigmaFinite ν] (ψ : AddChar A ℂ) (ι : Type) [Fintype ι] [DecidableEq ι] (Bm : Matrix ι ι A), Bm.IsSymm → MeasurableEmbedding (fun x : ι → A => Bm.mulVec x) → (Measure.pi fun _ : ι => ν).map (fun x => Bm.mulVec x) = (Measure.pi fun _ : ι => ν) → ∀ (t f : A → ℂ), (∀ y, f y = ∫ x, t x * ψ (x * y) ∂ν) → Integrable f ν → (∀ z, ∫ b, f b * ψ (b * z) ∂ν = t (-z)) → (∀ y, ∫ x : ι → A, (∏ i, t (x i)) * ψ (dotProduct x (Bm.mulVec y)) ∂(Measure.pi fun _ : ι => ν) = ∏ i, f (Bm.mulVec y i)) ∧ Integrable (fun y : ι → A => ∏ i, f (Bm.mulVec y i)) (Measure.pi fun _ : ι => ν) ∧ ∀ z : ι → A, ∫ y : ι → A, (∏ i, f (Bm.mulVec y i)) * ψ (dotProduct y (Bm.mulVec z)) ∂(Measure.pi fun _ : ι => ν) = ∏ i, t (-(z i)) := by sorry
