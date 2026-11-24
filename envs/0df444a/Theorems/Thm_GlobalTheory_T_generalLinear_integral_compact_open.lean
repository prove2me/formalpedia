-- Prove2me | Theorems.Thm_GlobalTheory_T_generalLinear_integral_compact_open
-- name    : GlobalTheory.T.generalLinear_integral_compact_open
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T13:47:36.244165+00:00
-- url     : https://prove2.me/theorems/d4ae821e-6a45-4c0d-90e7-da2c554562d5
-- title:
--   T: general Linear integral compact open
-- statement:
--   The T construction uses the general Linear integral compact open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/GeneralLinearIntegralCompactOpenStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/GeneralLinearIntegralCompactOpenStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_GeneralLinearIntegralCompactOpen
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_GeneralLinearIntegralCompactOpenStatement
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

theorem GlobalTheory.T.generalLinear_integral_compact_open : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ n : ℕ, IsOpen (GLint O n : Set (GL (Fin n) F)) ∧ IsCompact (GLint O n : Set (GL (Fin n) F)) ∧ LocallyCompactSpace (GL (Fin n) F) ∧ SecondCountableTopology (GL (Fin n) F) ∧ T2Space (GL (Fin n) F) ∧ IsOpen (Mint O n) ∧ IsClosed (Mint O n) := by sorry
