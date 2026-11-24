-- Prove2me | Theorems.Thm_GlobalTheory_HilbertSamuelPS_vector_val
-- name    : GlobalTheory.HilbertSamuelPS.vector_val
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T14:21:13.24824+00:00
-- url     : https://prove2.me/theorems/58533399-cbe8-495a-ace7-7d496466a71d
-- title:
--   Hilbert Samuel PS: vector val
-- statement:
--   The Hilbert Samuel PS construction uses the vector val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankMulPowLeFinrankOfPowerSeries.lean#L278-L305
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankMulPowLeFinrankOfPowerSeries.lean#L278-L305

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LinearIndependentOfDistinctValuationLikeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankLeCardValuesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankMulPowLeFinrankOfPowerSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
open GlobalTheory.HilbertSamuelPS
open MvPowerSeries
variable {D n : ℕ} {A : Type} [CommRing A] [Algebra ℂ A]
  {φ : Fin n → (A →ₐ[ℂ] MvPowerSeries (Fin D) ℂ)} {x : Fin D → A} {c : Fin D → ℂ}

theorem GlobalTheory.HilbertSamuelPS.vector_val (hx : ∀ j i, φ j (x i) = MvPowerSeries.X i + MvPowerSeries.C (c i))
    {m : ℕ} (hm : m ≠ 0) {b : A} (hb : ∃ k, evalAt φ k b ≠ 0) {e : Fin D →₀ ℕ}
    (he : lexOrder (evalAt φ (firstIdx φ b) b) = ((toLex e : Lex (Fin D →₀ ℕ)) : WithTop (Lex (Fin D →₀ ℕ))))
    (a : Fin D → ℕ) :
    b ^ m * ∏ d, (x d - algebraMap ℂ A (c d)) ^ a d ≠ 0 ∧
    val φ (b ^ m * ∏ d, (x d - algebraMap ℂ A (c d)) ^ a d) =
      toLex (firstIdx φ b, ((toLex (m • e + ∑ d, Finsupp.single d (a d)) : Lex (Fin D →₀ ℕ)) :
        WithTop (Lex (Fin D →₀ ℕ)))) := by sorry
