-- Prove2me | Theorems.Thm_GlobalTheory_TupleCone_isIntegral_ratioRing_iff_mem_adjoin
-- name    : GlobalTheory.TupleCone.isIntegral_ratioRing_iff_mem_adjoin
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:02:50.488807+00:00
-- url     : https://prove2.me/theorems/3a648ac1-9f35-5c3d-9e13-3686b3625071
-- title:
--   Tuple Cone: is Integral ratio Ring iff mem adjoin
-- statement:
--   The Tuple Cone construction uses the is Integral ratio Ring iff mem adjoin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIntegralRatioRingIffMemAdjoin.lean#L372-L408
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIntegralRatioRingIffMemAdjoin.lean#L372-L408

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteIntegralClosureOfEssFiniteTypeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIntegralRatioRingIffMemAdjoin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TupleCone
open Polynomial
variable (o : Type*) [CommRing o] {L : Type*} [Field L] [Algebra o L] {σ : Type*} (t : σ → L)
variable {o t}

theorem GlobalTheory.TupleCone.isIntegral_ratioRing_iff_mem_adjoin {τ : Type*} {z : τ → L} {e : ℕ} (he : 0 < e)
    (hz : Submodule.span o (Set.range z) = piece o t e)
    (hv : ∀ j, 0 < j → piece o t (j * e) = piece o t e ^ j) {i : σ} (hi : t i ≠ 0) {f : L} :
    IsIntegral (ratioRing o t i) f ↔
      f ∈ Algebra.adjoin o (Set.range fun k => z k / t i ^ e) := by sorry
