-- Prove2me | Theorems.Thm_GlobalTheory_SplitUnitary_hTens_eq
-- name    : GlobalTheory.SplitUnitary.hTens_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:58:52.233776+00:00
-- url     : https://prove2.me/theorems/ef6e5556-190b-49c1-b06d-6229ad492876
-- title:
--   Split Unitary: h Tens eq
-- statement:
--   The Split Unitary construction uses the h Tens eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/KudlaSplittingSplitUnitary.lean#L84-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/KudlaSplittingSplitUnitary.lean#L84-L91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_KudlaSplittingSplitUnitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open GlobalTheory GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG hTens IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB IsSmoothRep nabs)
variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
variable {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]
omit [DecidableEq α]

theorem GlobalTheory.SplitUnitary.hTens_eq (Q : Matrix α α E) (w w' : Matrix α (ν ⊕ ν) E) :
    hTens c Q (stdJ ν E) w w' = ∑ i, ∑ k, Q i k * (w * stdJ ν E * (w'.map c)ᵀ) i k := by sorry
