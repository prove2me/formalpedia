-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QLTop_nrm_le_one_iff
-- name    : GlobalTheory.CompanionTheory.QLTop.nrm_le_one_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:55:32.112994+00:00
-- url     : https://prove2.me/theorems/8c8c4ddc-f988-4d44-9551-c7b0ddcd9c27
-- title:
--   QLTop: nrm le one iff
-- statement:
--   The QLTop construction uses the nrm le one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/LocalFieldTopologyNormBalls.lean#L16-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/LocalFieldTopologyNormBalls.lean#L16-L67

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceOfIsNonarchimedeanLocalFieldFlagMeasures
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldTopologyNormBalls
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QLTop

theorem GlobalTheory.CompanionTheory.QLTop.nrm_le_one_iff {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ} (h : LF O ϖ nrm q) :
    1 < q ∧ ∀ x : F, nrm x ≤ 1 ↔ x ∈ O := by sorry
