-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_QIndex_BoxIndex_relIndex_line_pow
-- name    : GlobalTheory.CompanionTheory.QL.QIndex.BoxIndex.relIndex_line_pow
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:56:02.786855+00:00
-- url     : https://prove2.me/theorems/f06fc607-b9f5-4a75-80aa-edc578127b59
-- title:
--   Box Index: rel Index line pow
-- statement:
--   The Box Index construction uses the rel Index line pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/RelIndexBoxLatticesProduct.lean#L66-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/RelIndexBoxLatticesProduct.lean#L66-L79

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemConjSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_IsArtinianRingKummerAdjoinRootQuotientRoot
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_RelIndexBoxLatticesProduct
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.QIndex GlobalTheory.CompanionTheory.QL.QIndex.BoxIndex
open GlobalTheory.CompanionTheory.QL.NormalisedValue GlobalTheory.CompanionTheory.SplitRow.IdxV
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}

theorem GlobalTheory.CompanionTheory.QL.QIndex.BoxIndex.relIndex_line_pow (h : LF O ϖ nrm q) {c : F} (hc : c ≠ 0) (k : ℕ) :
    (line O (c * ϖ ^ k)).relIndex (line O c) = q ^ k := by sorry
