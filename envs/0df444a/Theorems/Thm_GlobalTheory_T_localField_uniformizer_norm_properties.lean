-- Prove2me | Theorems.Thm_GlobalTheory_T_localField_uniformizer_norm_properties
-- name    : GlobalTheory.T.localField_uniformizer_norm_properties
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:48.203817+00:00
-- url     : https://prove2.me/theorems/3e788310-4ed0-4423-8685-306002b092aa
-- title:
--   T: local Field uniformizer norm properties
-- statement:
--   The T construction uses the local Field uniformizer norm properties property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/LocalFieldUniformizerNormPropertiesStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/LocalFieldUniformizerNormPropertiesStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormPropertiesStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.localField_uniformizer_norm_properties : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → 1 < q ∧ ϖ ∈ O ∧ (∀ x : F, nrm x ≤ 1 ↔ x ∈ O) ∧ (∀ x : F, nrm x < 1 ↔ ∃ o ∈ O, x = ϖ * o) ∧ (∀ x : F, x ≠ 0 → ∃ e : ℤ, nrm x = (q : ℝ) ^ (-e) ∧ nrm (x * ϖ ^ (-e)) = 1) ∧ (∀ x y : F, nrm (x + y) ≤ max (nrm x) (nrm y)) ∧ (∀ x : F, nrm x = 1 ↔ ValuativeRel.valuation F x = 1) := by sorry
