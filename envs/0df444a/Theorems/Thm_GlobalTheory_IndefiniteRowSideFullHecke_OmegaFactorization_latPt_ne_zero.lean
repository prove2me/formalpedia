-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OmegaFactorization_latPt_ne_zero
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latPt_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:57:49.214297+00:00
-- url     : https://prove2.me/theorems/d12cf101-a570-4b7e-8160-aece113ad0a2
-- title:
--   Omega Factorization: lat Pt ne zero
-- statement:
--   The Omega Factorization construction uses the lat Pt ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/OmegaFactorization.lean#L227-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/OmegaFactorization.lean#L227-L245

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latPt_ne_zero {z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ}
    (hz : z ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F) {p : F × F} (hp : p ≠ 0) (τ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latPt z p τ ≠ 0 := by sorry
