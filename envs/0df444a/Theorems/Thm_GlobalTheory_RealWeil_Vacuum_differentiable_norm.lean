-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_Vacuum_differentiable_norm
-- name    : GlobalTheory.RealWeil.Vacuum.differentiable_norm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:58:08.13299+00:00
-- url     : https://prove2.me/theorems/ef3de65f-a70a-4a06-a891-5c3ebbf6d421
-- title:
--   Vacuum: differentiable norm
-- statement:
--   The Vacuum construction uses the differentiable norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProjEqSelfOfAnnihilated.lean#L14-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProjEqSelfOfAnnihilated.lean#L14-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProjEqSelfOfAnnihilated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
open GlobalTheory GlobalTheory.RealWeil GlobalTheory.RealWeil.Vacuum
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] {J : V ≃ₗᵢ[ℝ] V} {ρ : V → B →L[ℂ] B}

theorem GlobalTheory.RealWeil.Vacuum.differentiable_norm (f : B) (hf : Sm ρ f) : Differentiable ℝ fun u => (gau u)⁻¹ • ρ u f := by sorry
