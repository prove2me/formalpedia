-- Prove2me | Theorems.Thm_GlobalTheory_IdealSum_tsum_ideal_eq_sum_classes
-- name    : GlobalTheory.IdealSum.tsum_ideal_eq_sum_classes
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:04:33.819873+00:00
-- url     : https://prove2.me/theorems/2f71ffc9-42bb-428e-b1b6-d498a3670dd4
-- title:
--   Ideal Sum: tsum ideal eq sum classes
-- statement:
--   The Ideal Sum construction uses the tsum ideal eq sum classes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IdealSumPeriodicDilate.lean#L8-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IdealSumPeriodicDilate.lean#L8-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LatticeSumDilateHaarAsymptoticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdealSumPeriodicDilate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open GlobalTheory GlobalTheory.IdealSum

theorem GlobalTheory.IdealSum.tsum_ideal_eq_sum_classes {R : Type} [CommRing R] (m b : Ideal R) [Fintype (R ⧸ m)]
    (hbm : b ⊔ m = ⊤) (s : R ⧸ m → R) (hsb : ∀ r, s r ∈ b)
    (hs : ∀ r, Ideal.Quotient.mk m (s r) = r) (ψ g : R → ℂ)
    (hψ : ∀ a b, a - b ∈ m → ψ a = ψ b) (hg : Summable fun α : b => ψ α * g α) :
    ∑' α : b, ψ α * g α = ∑ r : R ⧸ m, ψ (s r) * ∑' β : ↥(b * m), g ((β : R) + s r) := by sorry
