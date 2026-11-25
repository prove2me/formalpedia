-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_HaarGL_exists_haar_unimodular
-- name    : GlobalTheory.CompanionTheory.QL.HaarGL.exists_haar_unimodular
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:02:32.624812+00:00
-- url     : https://prove2.me/theorems/c2ea89c3-301a-4381-add4-571ec6e41495
-- title:
--   Haar GL: exists haar unimodular
-- statement:
--   The Haar GL construction uses the exists haar unimodular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/GeneralLinearUnimodularHaar.lean#L9-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/GeneralLinearUnimodularHaar.lean#L9-L24

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_GeneralLinearIntegralCompactOpenStatement
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_GeneralLinearUnimodularHaar
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.HaarGL

theorem GlobalTheory.CompanionTheory.QL.HaarGL.exists_haar_unimodular : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ n : ℕ, (∃ κ : Measure (GL (Fin n) F), κ.IsMulLeftInvariant ∧ κ (GLint O n : Set (GL (Fin n) F)) = 1) ∧ ∀ μ : Measure (GL (Fin n) F), μ.IsHaarMeasure → μ.IsMulRightInvariant ∧ μ.IsInvInvariant := by sorry
