-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QLTop_gl_topology
-- name    : GlobalTheory.CompanionTheory.QLTop.gl_topology
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:56:14.076203+00:00
-- url     : https://prove2.me/theorems/6a8a5e16-4143-4372-b14d-1f1dcbd9e3c2
-- title:
--   QLTop: gl topology
-- statement:
--   The QLTop construction uses the gl topology property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/GeneralLinearIntegralCompactOpen.lean#L60-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/GeneralLinearIntegralCompactOpen.lean#L60-L86

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_GeneralLinearIntegralCompactOpen
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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QLTop
open ValuativeRel
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem GlobalTheory.CompanionTheory.QLTop.gl_topology : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ n : ℕ,
    IsOpen (GLint O n : Set (GL (Fin n) F)) ∧ IsCompact (GLint O n : Set (GL (Fin n) F)) ∧
    LocallyCompactSpace (GL (Fin n) F) ∧ SecondCountableTopology (GL (Fin n) F) ∧ T2Space (GL (Fin n) F) ∧
    IsOpen (Mint O n) ∧ IsClosed (Mint O n) := by sorry
