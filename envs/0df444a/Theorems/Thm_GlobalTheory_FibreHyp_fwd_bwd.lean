-- Prove2me | Theorems.Thm_GlobalTheory_FibreHyp_fwd_bwd
-- name    : GlobalTheory.FibreHyp.fwd_bwd
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:24:13.938942+00:00
-- url     : https://prove2.me/theorems/77bf170c-19a8-4920-97f5-ce8c4ec7600e
-- title:
--   Fibre Hyp: fwd bwd
-- statement:
--   The Fibre Hyp construction uses the fwd bwd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PreirreducibleSpaceFibreHypersurfaceSpectrumIff.lean#L89-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PreirreducibleSpaceFibreHypersurfaceSpectrumIff.lean#L89-L101

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

theorem GlobalTheory.FibreHyp.fwd_bwd : (fwd f g k).comp (bwd2 f g k) = AlgHom.id k _ := by sorry
