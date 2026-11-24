-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QLTop_localField_top
-- name    : GlobalTheory.CompanionTheory.QLTop.localField_top
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:55:33.820644+00:00
-- url     : https://prove2.me/theorems/4d074b19-4fd2-4a1d-84de-45a1f015c7e2
-- title:
--   QLTop: local Field top
-- statement:
--   The QLTop construction uses the local Field top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/LocalFieldTopologyNormBalls.lean#L69-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/LocalFieldTopologyNormBalls.lean#L69-L115

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

theorem GlobalTheory.CompanionTheory.QLTop.localField_top : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → IsOpen (O : Set F) ∧ IsCompact (O : Set F) ∧ SecondCountableTopology F ∧ Continuous (fun x : F => nrm x) ∧ (∀ e : ℤ, IsOpen {x : F | nrm x ≤ (q : ℝ) ^ e}) ∧ (∀ s ∈ nhds (0 : F), ∃ e : ℤ, {x : F | nrm x ≤ (q : ℝ) ^ e} ⊆ s) := by sorry
