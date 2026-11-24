-- Prove2me | Theorems.Thm_GlobalTheory_WrongSignGauss_ip_smul_left
-- name    : GlobalTheory.WrongSignGauss.ip_smul_left
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:18:51.17762+00:00
-- url     : https://prove2.me/theorems/863869e0-6539-4890-87f6-2088e6c9f107
-- title:
--   Wrong Sign Gauss: ip smul left
-- statement:
--   The Wrong Sign Gauss construction uses the ip smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SchwartzEqZeroOfWrongSignGaussianRelation.lean#L65-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SchwartzEqZeroOfWrongSignGaussianRelation.lean#L65-L67

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

theorem GlobalTheory.WrongSignGauss.ip_smul_left (c : ℂ) (u w : 𝓢(V, ℂ)) : ip μ (c • u) w = c * ip μ u w := by sorry
