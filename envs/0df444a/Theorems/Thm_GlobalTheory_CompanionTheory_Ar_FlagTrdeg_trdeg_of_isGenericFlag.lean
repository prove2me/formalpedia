-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_FlagTrdeg_trdeg_of_isGenericFlag
-- name    : GlobalTheory.CompanionTheory.Ar.FlagTrdeg.trdeg_of_isGenericFlag
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:59:09.682413+00:00
-- url     : https://prove2.me/theorems/900c43de-97d2-4709-85b1-1e13316b430d
-- title:
--   Flag Trdeg: trdeg of is Generic Flag
-- statement:
--   The Flag Trdeg construction uses the trdeg of is Generic Flag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/GenericFlagTrdegFormula.lean#L32-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/GenericFlagTrdegFormula.lean#L32-L64

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsGenericFlag
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_GenericFlagTrdegFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.CompanionTheory.Ar
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagTrdeg
open scoped IntermediateField.algebraAdjoinAdjoin

theorem GlobalTheory.CompanionTheory.Ar.FlagTrdeg.trdeg_of_isGenericFlag (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [Algebra Ω₀ Ω] (E : Type) [AddCommGroup E]
    [Module Ω₀ E] (E' : Type) [AddCommGroup E'] [Module Ω E'] (j : E →+ E') (S : Type) [Fintype S]
    (r : S → ℕ) (V : S → Submodule Ω₀ E) (b₀ : ∀ σ, Fin (r σ) → E') (d : ℕ)
    (hg : IsGenericFlag (Ω' := Ω) j V b₀ d) :
    Algebra.trdeg Ω₀ Ω = ((∑ σ, r σ * (r σ - 1) / 2 : ℕ) : Cardinal) := by sorry
