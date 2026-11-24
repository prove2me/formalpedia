-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_summable_balanced_latSum
-- name    : GlobalTheory.HeckeTwo.summable_balanced_latSum
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:13:13.530496+00:00
-- url     : https://prove2.me/theorems/ce5d10ed-729f-43a3-a938-1a060a5cdb99
-- title:
--   Hecke Two: summable balanced lat Sum
-- statement:
--   The Hecke Two construction uses the summable balanced lat Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableHeckeBalancedLatticeDoubleSum.lean#L122-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableHeckeBalancedLatticeDoubleSum.lean#L122-L245

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableHeckeBalancedLatticeDoubleSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory.HeckeTwo.LatSum

theorem GlobalTheory.HeckeTwo.summable_balanced_latSum :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔞 𝔟 : Frac F) (C₀ : ℝ) (m : ℕ), ∃ N : ℕ,
    ∀ ε : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) → (𝓞 F)ˣ,
      (∀ c (τ τ' : Emb F), |τ (((ε c : 𝓞 F) : F) * c.out.1)| ≤ C₀ * |τ' (((ε c : 𝓞 F) : F) * c.out.1)|) →
      Summable (fun p : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) × NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) =>
        ∏ τ : Emb F, (|τ (((ε p.1 : 𝓞 F) : F) * p.1.out.1)| + |τ (((ε p.1 : 𝓞 F) : F) * p.1.out.1)|⁻¹) ^ m /
          (1 + |τ p.2.1 * τ p.1.out.1|) ^ N) := by sorry
