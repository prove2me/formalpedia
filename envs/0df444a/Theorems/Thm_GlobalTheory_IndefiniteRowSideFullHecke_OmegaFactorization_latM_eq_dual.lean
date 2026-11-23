-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OmegaFactorization_latM_eq_dual
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM_eq_dual
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:57:14.02581+00:00
-- url     : https://prove2.me/theorems/641afdf3-dd93-41c6-8ae4-f5d84f02d1bc
-- title:
--   Omega Factorization: lat M eq dual
-- statement:
--   The Omega Factorization construction uses the lat M eq dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/OmegaFactorization.lean#L32-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/OmegaFactorization.lean#L32-L37

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM_eq_dual (𝔞 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞 =
      FractionalIdeal.dual ℤ ℚ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) := by sorry
