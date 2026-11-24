-- Prove2me | Theorems.Thm_GlobalTheory_WrongSignGauss_ip_sub_right
-- name    : GlobalTheory.WrongSignGauss.ip_sub_right
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:57:41.786771+00:00
-- url     : https://prove2.me/theorems/82e0bd31-95f8-4e3b-9f62-504ea76e1b39
-- title:
--   Wrong Sign Gauss: ip sub right
-- statement:
--   The Wrong Sign Gauss construction uses the ip sub right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SchwartzEqZeroOfWrongSignGaussianRelation.lean#L78-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SchwartzEqZeroOfWrongSignGaussianRelation.lean#L78-L80

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

theorem GlobalTheory.WrongSignGauss.ip_sub_right (u v w : 𝓢(V, ℂ)) : ip μ w (u - v) = ip μ w u - ip μ w v := by sorry
