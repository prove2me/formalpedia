-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_QIndex_ConjLe_mem_congGL_of_lvl
-- name    : GlobalTheory.CompanionTheory.QL.QIndex.ConjLe.mem_congGL_of_lvl
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:55:56.698574+00:00
-- url     : https://prove2.me/theorems/8fdd2c24-5768-4c9d-b6df-de4383897d6c
-- title:
--   Conj Le: mem cong GL of lvl
-- statement:
--   The Conj Le construction uses the mem cong GL of lvl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DiagonalConjugateCongruenceBox.lean#L97-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DiagonalConjugateCongruenceBox.lean#L97-L124

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemConjSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemIntegralGLIffIntegralUnitDet
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DiagonalConjugateCongruenceBox
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.QIndex
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.QIndex GlobalTheory.CompanionTheory.QL.QIndex.ConjLe
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}

theorem GlobalTheory.CompanionTheory.QL.QIndex.ConjLe.mem_congGL_of_lvl (hLF : LF O ϖ nrm q) {n T : ℕ} (hT : 1 ≤ T) (g : GL (Fin n) F)
    (h : Lvl O (ϖ ^ T) ((g : Matrix (Fin n) (Fin n) F) - 1)) : g ∈ congGL O (ϖ ^ T) n := by sorry
