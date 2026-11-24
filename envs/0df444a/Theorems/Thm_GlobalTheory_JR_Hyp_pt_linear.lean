-- Prove2me | Theorems.Thm_GlobalTheory_JR_Hyp_pt_linear
-- name    : GlobalTheory.JR.Hyp.pt_linear
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:35:14.621503+00:00
-- url     : https://prove2.me/theorems/3090be36-3e8e-4982-8ee8-62c7daee3602
-- title:
--   Hyp: pt linear
-- statement:
--   The Hyp construction uses the pt linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HyperbolicPartialFourierLinearOnTest.lean#L9-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HyperbolicPartialFourierLinearOnTest.lean#L9-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WHyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HyperbolicPartialFourierLinearOnTest
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Hyp

theorem GlobalTheory.JR.Hyp.pt_linear : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.K) (ν : Measure A.K), ν.IsAddHaarMeasure → ∀ (c : ℂ) (Φ Φ' : A.K × A.K → ℂ), IsTest Φ → IsTest Φ' → Hyp.pt A ν ψ x (c • Φ + Φ') = c • Hyp.pt A ν ψ x Φ + Hyp.pt A ν ψ x Φ' := by sorry
