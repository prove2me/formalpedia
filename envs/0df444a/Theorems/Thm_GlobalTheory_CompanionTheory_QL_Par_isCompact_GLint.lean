-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_Par_isCompact_GLint
-- name    : GlobalTheory.CompanionTheory.QL.Par.isCompact_GLint
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:56:19.839555+00:00
-- url     : https://prove2.me/theorems/bd1a7035-f153-4124-b299-a94d58b35ac8
-- title:
--   Par: is Compact GLint
-- statement:
--   The Par construction uses the is Compact GLint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ParahoricSubgroupCompactOpenMeasure.lean#L166-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ParahoricSubgroupCompactOpenMeasure.lean#L166-L176

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParahoricSubgroupCompactOpenMeasure
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.Par
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}

theorem GlobalTheory.CompanionTheory.QL.Par.isCompact_GLint (h : LF O ϖ nrm q) (n : ℕ) : IsCompact (GLint O n : Set (GL (Fin n) F)) := by sorry
