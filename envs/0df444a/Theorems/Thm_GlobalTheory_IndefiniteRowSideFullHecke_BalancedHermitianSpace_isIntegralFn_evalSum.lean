-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_BalancedHermitianSpace_isIntegralFn_evalSum
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace.isIntegralFn_evalSum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:46:17.36581+00:00
-- url     : https://prove2.me/theorems/8d441b80-b4a2-4ea7-b8e9-d870c177fdfe
-- title:
--   Balanced Hermitian Space: is Integral Fn eval Sum
-- statement:
--   The Balanced Hermitian Space construction uses the is Integral Fn eval Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/BalancedHermitianSpace.lean#L130-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/BalancedHermitianSpace.lean#L130-L138

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_BalancedHermitianSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace
open NumberField NumberField.IsCMField TensorProduct
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
variable {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y]
open NumberField NumberField.IsCMField TensorProduct
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
variable {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y]
omit [NumberField E] [IsCMField E] [Module (𝓞 E) Y]

theorem GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace.isIntegralFn_evalSum (S : Submodule ℝ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace.Bil Y))
    {k : ℕ} (x x' : Fin k → Y) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace.IsIntegralFn S (_root_.GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace.evalSum S x x') := by sorry
