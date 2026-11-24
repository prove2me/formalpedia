-- Prove2me | Theorems.Thm_GlobalTheory_FibreHyp_bwd_fwd
-- name    : GlobalTheory.FibreHyp.bwd_fwd
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:24:32.574627+00:00
-- url     : https://prove2.me/theorems/8debeb21-0b99-4880-bec5-fd8263e869e1
-- title:
--   Fibre Hyp: bwd fwd
-- statement:
--   The Fibre Hyp construction uses the bwd fwd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PreirreducibleSpaceFibreHypersurfaceSpectrumIff.lean#L103-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PreirreducibleSpaceFibreHypersurfaceSpectrumIff.lean#L103-L117

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

theorem GlobalTheory.FibreHyp.bwd_fwd : (bwd2 f g k).comp (fwd f g k) = AlgHom.id k _ := by sorry
