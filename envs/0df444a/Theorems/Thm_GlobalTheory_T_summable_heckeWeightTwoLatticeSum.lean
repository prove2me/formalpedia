-- Prove2me | Theorems.Thm_GlobalTheory_T_summable_heckeWeightTwoLatticeSum
-- name    : GlobalTheory.T.summable_heckeWeightTwoLatticeSum
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:00:06.900816+00:00
-- url     : https://prove2.me/theorems/2df7f868-96e3-41e3-a8b0-c63e4a30b1ba
-- title:
--   T: summable hecke Weight Two Lattice Sum
-- statement:
--   The T construction uses the summable hecke Weight Two Lattice Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableHeckeWeightTwoLatticeSumStatement.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableHeckeWeightTwoLatticeSumStatement.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableHeckeWeightTwoLatticeSum
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableHeckeWeightTwoLatticeSumStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.summable_heckeWeightTwoLatticeSum : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (σ : ℂ), 0 < σ.re → ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, ∀ b : F, b ≠ 0 → Summable (fun a : {a : F // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞} => ∏ τ : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, GlobalTheory.HeckeTwo.phi σ (((τ a.1 : ℝ) : ℂ) + ((τ b : ℝ) : ℂ) * z τ)) := by sorry
