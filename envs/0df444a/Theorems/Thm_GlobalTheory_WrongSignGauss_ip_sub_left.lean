-- Prove2me | Theorems.Thm_GlobalTheory_WrongSignGauss_ip_sub_left
-- name    : GlobalTheory.WrongSignGauss.ip_sub_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:18:40.297814+00:00
-- url     : https://prove2.me/theorems/352567d0-57c6-4c35-8ffd-6819e84aa1c3
-- title:
--   Wrong Sign Gauss: ip sub left
-- statement:
--   The Wrong Sign Gauss construction uses the ip sub left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SchwartzEqZeroOfWrongSignGaussianRelation.lean#L74-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SchwartzEqZeroOfWrongSignGaussianRelation.lean#L74-L76

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

theorem GlobalTheory.WrongSignGauss.ip_sub_left (u v w : 𝓢(V, ℂ)) : ip μ (u - v) w = ip μ u w - ip μ v w := by sorry
