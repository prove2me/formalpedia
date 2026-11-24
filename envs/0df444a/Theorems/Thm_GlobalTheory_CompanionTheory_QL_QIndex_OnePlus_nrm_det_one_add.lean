-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_QIndex_OnePlus_nrm_det_one_add
-- name    : GlobalTheory.CompanionTheory.QL.QIndex.OnePlus.nrm_det_one_add
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:55:58.097876+00:00
-- url     : https://prove2.me/theorems/3f03004e-14ad-46c1-9ebe-a8738d9522df
-- title:
--   One Plus: nrm det one add
-- statement:
--   The One Plus construction uses the nrm det one add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/MemBoxLatticeIffCongruence.lean#L10-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/MemBoxLatticeIffCongruence.lean#L10-L57

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemConjSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemIntegralGLIffIntegralUnitDet
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemBoxLatticeIffCongruence
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.QIndex GlobalTheory.CompanionTheory.QL.QIndex.OnePlus

theorem GlobalTheory.CompanionTheory.QL.QIndex.OnePlus.nrm_det_one_add {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}
    (hLF : LF O ϖ nrm q) {n : ℕ} {x : Matrix (Fin n) (Fin n) F}
    (hx : ∀ a b, ∃ o ∈ O, x a b = ϖ * o) : nrm (1 + x).det = 1 := by sorry
