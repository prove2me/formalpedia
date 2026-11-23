-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OmegaFactorization_qClass_mk
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:57:56.185583+00:00
-- url     : https://prove2.me/theorems/2fbbe1fd-49da-4843-aff2-b599b0bc06fd
-- title:
--   Omega Factorization: q Class mk
-- statement:
--   The Omega Factorization construction uses the q Class mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/OmegaFactorization.lean#L206-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/OmegaFactorization.lean#L206-L220

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass_mk (𝔞 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (k : ℕ)
    (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) (p : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.QPair 𝔞 𝔟) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass 𝔞 𝔟 k z (Quotient.mk _ p) =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qTerm 𝔞 k z p.1 := by sorry
