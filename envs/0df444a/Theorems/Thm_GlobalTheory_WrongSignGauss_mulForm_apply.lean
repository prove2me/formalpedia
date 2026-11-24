-- Prove2me | Theorems.Thm_GlobalTheory_WrongSignGauss_mulForm_apply
-- name    : GlobalTheory.WrongSignGauss.mulForm_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:38.12544+00:00
-- url     : https://prove2.me/theorems/6742446c-5b71-47fd-a4c3-cf762ed5c4ba
-- title:
--   Wrong Sign Gauss: mul Form apply
-- statement:
--   The Wrong Sign Gauss construction uses the mul Form apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SchwartzEqZeroOfWrongSignGaussianRelation.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SchwartzEqZeroOfWrongSignGaussianRelation.lean#L20-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzEqZeroOfWrongSignGaussianRelation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open SchwartzMap LineDeriv MeasureTheory ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.WrongSignGauss
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem GlobalTheory.WrongSignGauss.mulForm_apply (ℓ : V →ₗ[ℝ] ℝ) (f : 𝓢(V, ℂ)) (x : V) :
    mulForm ℓ f x = (ℓ x : ℂ) * f x := by sorry
