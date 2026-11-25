-- Prove2me | Theorems.Thm_GlobalTheory_ThKOp_continuous_of_mem_schA
-- name    : GlobalTheory.ThKOp.continuous_of_mem_schA
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:41:04.021258+00:00
-- url     : https://prove2.me/theorems/9763743b-dc88-4fa1-9930-7a78f59a1448
-- title:
--   Th KOp: continuous of mem sch A
-- statement:
--   The Th KOp construction uses the continuous of mem sch A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousOfMemSchA.lean#L12-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousOfMemSchA.lean#L12-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfMemSchA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.WeilM
open GlobalTheory GlobalTheory.ThKOp
open scoped Classical

theorem GlobalTheory.ThKOp.continuous_of_mem_schA {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ schA F κ) : Continuous Φ := by sorry
