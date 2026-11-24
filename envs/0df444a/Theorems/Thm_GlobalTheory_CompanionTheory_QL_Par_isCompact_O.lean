-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_Par_isCompact_O
-- name    : GlobalTheory.CompanionTheory.QL.Par.isCompact_O
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:56:29.356262+00:00
-- url     : https://prove2.me/theorems/e75cb3e7-2468-401f-a78b-af804c12c714
-- title:
--   Par: is Compact O
-- statement:
--   The Par construction uses the is Compact O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ParahoricSubgroupCompactOpenMeasure.lean#L134-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ParahoricSubgroupCompactOpenMeasure.lean#L134-L136

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

theorem GlobalTheory.CompanionTheory.QL.Par.isCompact_O (h : LF O ϖ nrm q) : IsCompact (O : Set F) := by sorry
