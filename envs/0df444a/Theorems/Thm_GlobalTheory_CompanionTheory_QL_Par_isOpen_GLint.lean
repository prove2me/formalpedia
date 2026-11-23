-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_Par_isOpen_GLint
-- name    : GlobalTheory.CompanionTheory.QL.Par.isOpen_GLint
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:16.425312+00:00
-- url     : https://prove2.me/theorems/8f970cdb-d7d5-4949-8cc4-8f42305d5771
-- title:
--   Par: is Open GLint
-- statement:
--   The Par construction uses the is Open GLint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ParahoricSubgroupCompactOpenMeasure.lean#L138-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ParahoricSubgroupCompactOpenMeasure.lean#L138-L155

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

theorem GlobalTheory.CompanionTheory.QL.Par.isOpen_GLint (h : LF O ϖ nrm q) (n : ℕ) : IsOpen (GLint O n : Set (GL (Fin n) F)) := by sorry
