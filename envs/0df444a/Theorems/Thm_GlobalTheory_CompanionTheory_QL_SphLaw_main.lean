-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_SphLaw_main
-- name    : GlobalTheory.CompanionTheory.QL.SphLaw.main
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:02:31.128082+00:00
-- url     : https://prove2.me/theorems/f00bd2a9-08b3-439b-bf04-27d029a27e18
-- title:
--   Sph Law: main
-- statement:
--   The Sph Law construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/SphericalFunctionInvarianceProperties.lean#L64-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/SphericalFunctionInvarianceProperties.lean#L64-L111

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormPropertiesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_GeneralLinearIntegralCompactOpenStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IwasawaDecompositionUpperTriangularStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_SphericalFunctionInvarianceProperties
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_NormalisedValue_main

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.SphLaw

theorem GlobalTheory.CompanionTheory.QL.SphLaw.main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ {c : ℕ} (χ : Fin c → F → ℂ) (α : Fin c → ℂ), UnrChar nrm q χ α → ∀ (φ : GL (Fin c) F → ℂ), IsSphFn O nrm χ φ → (∀ k ∈ GLint O c, φ k = 1) ∧ (∀ g, ∀ k ∈ GLint O c, φ (g * k) = φ g) ∧ (∀ b : GL (Fin c) F, (b : Matrix (Fin c) (Fin c) F).BlockTriangular id → ∀ g, φ (b * g) = φ b * φ g) ∧ Continuous φ ∧ ∀ φ', IsSphFn O nrm χ φ' → φ' = φ := by sorry
