-- Prove2me | Theorems.Thm_GlobalTheory_SplitUnitary_heisFun_levi
-- name    : GlobalTheory.SplitUnitary.heisFun_levi
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:24:30.037408+00:00
-- url     : https://prove2.me/theorems/4ec73778-fa46-4fef-b5ec-fa60e4659f59
-- title:
--   Split Unitary: heis Fun levi
-- statement:
--   The Split Unitary construction uses the heis Fun levi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/KudlaSplittingSplitUnitary.lean#L161-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/KudlaSplittingSplitUnitary.lean#L161-L173

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

theorem GlobalTheory.SplitUnitary.heisFun_levi (hc : ∀ z, c (c z) = z) (ψ : AddChar F ℂ) (Q : Matrix α α E) (a : GL ν E) (w : Matrix α (ν ⊕ ν) E)
    (φ : Matrix α ν E → ℂ) :
    heisFun c ψ Q w (fun x => φ (x * (a : Matrix ν ν E))) =
      fun x => heisFun c ψ Q (w * ((levi c hc a : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E)) φ (x * (a : Matrix ν ν E)) := by sorry
