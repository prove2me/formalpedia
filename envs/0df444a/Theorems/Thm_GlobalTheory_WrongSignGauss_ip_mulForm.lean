-- Prove2me | Theorems.Thm_GlobalTheory_WrongSignGauss_ip_mulForm
-- name    : GlobalTheory.WrongSignGauss.ip_mulForm
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:57:19.454803+00:00
-- url     : https://prove2.me/theorems/ed023b6a-8a49-4a55-8c51-715d86dab111
-- title:
--   Wrong Sign Gauss: ip mul Form
-- statement:
--   The Wrong Sign Gauss construction uses the ip mul Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SchwartzEqZeroOfWrongSignGaussianRelation.lean#L87-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SchwartzEqZeroOfWrongSignGaussianRelation.lean#L87-L89

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
variable [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]

theorem GlobalTheory.WrongSignGauss.ip_mulForm (ℓ : V →ₗ[ℝ] ℝ) (u w : 𝓢(V, ℂ)) : ip μ (mulForm ℓ u) w = ip μ u (mulForm ℓ w) := by sorry
