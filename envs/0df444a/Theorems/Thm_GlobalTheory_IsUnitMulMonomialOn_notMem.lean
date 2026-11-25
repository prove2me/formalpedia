-- Prove2me | Theorems.Thm_GlobalTheory_IsUnitMulMonomialOn_notMem
-- name    : GlobalTheory.IsUnitMulMonomialOn.notMem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:55:03.96201+00:00
-- url     : https://prove2.me/theorems/3b18dd64-2ffc-4751-a77a-6441804aeff5
-- title:
--   Is Unit Mul Monomial On: not Mem
-- statement:
--   The Is Unit Mul Monomial On construction uses the not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean#L197-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean#L197-L203

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set Filter
open scoped ComplexOrder MatrixOrder Kronecker Topology
open GlobalTheory
variable {κ κ' X X' E F : Type*} [TopologicalSpace X] [TopologicalSpace X']
  [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
variable {S : Finset κ} {w : X → κ → ℂ} {U : Set X}
open GlobalTheory.IsUnitMulMonomialOn
variable {S' : Finset κ'} {w' : X' → κ' → ℂ} {U' : Set X'} {v : X' → κ → ℂ}

theorem GlobalTheory.IsUnitMulMonomialOn.notMem (h : IsUnitMulMonomialOn S v S' w' U') {x : X'} (hx : x ∈ U')
    (hB : x ∉ coordDivisor S' w') : x ∉ coordDivisor S v := by sorry
