-- Prove2me | Theorems.Thm_GlobalTheory_DualCokernel_extZero_self
-- name    : GlobalTheory.DualCokernel.extZero_self
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:06:15.176172+00:00
-- url     : https://prove2.me/theorems/7e632f74-d819-4a6f-9ca1-aad4c91ed387
-- title:
--   Dual Cokernel: ext Zero self
-- statement:
--   The Dual Cokernel construction uses the ext Zero self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsSMulRegularCokerDualMapOfExactFibres.lean#L177-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsSMulRegularCokerDualMapOfExactFibres.lean#L177-L211

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_AcyclicityLemmaDepthDifferentialCokernelsFiniteL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndKerBaseChangeOfForallResidueField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsSMulRegularCokerDualMapOfExactFibres
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian IsLocalRing TensorProduct Function
open GlobalTheory
open GlobalTheory.DualCokernel
variable {R : Type} [CommRing R]
variable [IsLocalRing R]
variable [IsNoetherianRing R]

theorem GlobalTheory.DualCokernel.extZero_self (ϖ : R) (g : ℕ) (hϖ : ϖ ∈ nonZeroDivisors R) (hm : ϖ ∈ maximalIdeal R)
    [IsRegularLocalRing (R ⧸ Ideal.span {ϖ})] (hg : ringKrullDim (R ⧸ Ideal.span {ϖ}) = g)
    (j : ℕ) (hj : j < g + 1) : ExtZero (R := R) R j := by sorry
