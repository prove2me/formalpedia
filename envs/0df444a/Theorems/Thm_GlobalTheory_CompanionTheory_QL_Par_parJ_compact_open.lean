-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_Par_parJ_compact_open
-- name    : GlobalTheory.CompanionTheory.QL.Par.parJ_compact_open
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:56:09.833611+00:00
-- url     : https://prove2.me/theorems/6ae588fb-8ab3-4f40-9a52-b959645fc1ed
-- title:
--   Par: par J compact open
-- statement:
--   The Par construction uses the par J compact open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ParahoricSubgroupCompactOpenMeasure.lean#L200-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ParahoricSubgroupCompactOpenMeasure.lean#L200-L216

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

theorem GlobalTheory.CompanionTheory.QL.Par.parJ_compact_open : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ},
    LF O ϖ nrm q → ∀ r c : ℕ, ∃ J : Subgroup (GL (Fin (r + c)) F),
      (J : Set (GL (Fin (r + c)) F)) = parJ O ϖ r c ∧ IsOpen (parJ O ϖ r c) ∧
      IsCompact (parJ O ϖ r c) ∧ ∃ μ : Measure (GL (Fin (r + c)) F), μ.IsMulLeftInvariant ∧
        μ (parJ O ϖ r c) = 1 := by sorry
