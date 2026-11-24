-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_QIndex_mem_conjSub
-- name    : GlobalTheory.CompanionTheory.QL.QIndex.mem_conjSub
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:56:24.994799+00:00
-- url     : https://prove2.me/theorems/3cb1ede5-904c-4e55-a56e-349740430a79
-- title:
--   QIndex: mem conj Sub
-- statement:
--   The QIndex construction uses the mem conj Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/MemConjSub.lean#L72-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/MemConjSub.lean#L72-L79

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemConjSub
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.QIndex
variable {F : Type} [Field F]

theorem GlobalTheory.CompanionTheory.QL.QIndex.mem_conjSub {G : Type} [Group G] (H : Subgroup G) (d p : G) :
    p ∈ conjSub H d ↔ d * p * d⁻¹ ∈ H := by sorry
