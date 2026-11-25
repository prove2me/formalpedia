-- Prove2me | Theorems.Thm_GlobalTheory_T_chernCurvature_form_self_eq_dual_norm
-- name    : GlobalTheory.T.chernCurvature_form_self_eq_dual_norm
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:55:04.744163+00:00
-- url     : https://prove2.me/theorems/211e4c62-24f8-442e-9515-93fd530e4878
-- title:
--   T: chern Curvature form self eq dual norm
-- statement:
--   The T construction uses the chern Curvature form self eq dual norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ChernCurvatureFormSelfEqDualNormStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ChernCurvatureFormSelfEqDualNormStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ChernCurvatureFormSelfEqDualNorm
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ChernCurvatureFormSelfEqDualNormStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.chernCurvature_form_self_eq_dual_norm : ∀ (n g : ℕ) (H : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (z : Fin n → ℂ), MContDiffAt 2 H z → IsUnit (H z).det → (∀ᶠ x in 𝓝 z, (H x).IsSymm) → (∀ᶠ x in 𝓝 z, (H x).IsHermitian) → (∀ ξ η, mddbar H z ξ η = 0) → ∀ ξ v, form (H z) (curv H z ξ ξ *ᵥ v) v = form (H z)⁻¹ (mdel H z ξ *ᵥ v) (mdel H z ξ *ᵥ v) := by sorry
