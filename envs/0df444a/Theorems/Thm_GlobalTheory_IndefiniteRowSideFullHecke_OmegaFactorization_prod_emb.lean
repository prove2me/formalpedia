-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OmegaFactorization_prod_emb
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.prod_emb
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:08.457918+00:00
-- url     : https://prove2.me/theorems/56d11d6c-75e5-48d1-bd65-eb1db2b36e2b
-- title:
--   Omega Factorization: prod emb
-- statement:
--   The Omega Factorization construction uses the prod emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/OmegaFactorization.lean#L141-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/OmegaFactorization.lean#L141-L160

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.prod_emb [IsTotallyReal F] (x : F) :
    ∏ τ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, ((τ x : ℝ) : ℂ) = ((Algebra.norm ℚ x : ℚ) : ℂ) := by sorry
