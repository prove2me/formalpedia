-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OmegaFactorization_eisClass_mk
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass_mk
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:14:41.822387+00:00
-- url     : https://prove2.me/theorems/a8144d32-e621-4b0a-9149-138c5c765e65
-- title:
--   Omega Factorization: eis Class mk
-- statement:
--   The Omega Factorization construction uses the eis Class mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/OmegaFactorization.lean#L189-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/OmegaFactorization.lean#L189-L199

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
variable (F : Type) [Field F] [NumberField F]
variable {F}
open NumberField Complex
open scoped nonZeroDivisors ContDiff
variable (F : Type) [Field F] [NumberField F]
variable {F}

theorem GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass_mk [IsTotallyReal F] (𝔞 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F)
    {k : ℕ} (hk : Even k) (σ : ℂ) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ)
    (p : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.LatPair 𝔞 𝔟) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 k σ z (Quotient.mk _ p) =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisTerm k σ z p.1 := by sorry
