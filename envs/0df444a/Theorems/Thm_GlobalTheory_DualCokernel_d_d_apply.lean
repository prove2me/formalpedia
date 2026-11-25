-- Prove2me | Theorems.Thm_GlobalTheory_DualCokernel_d_d_apply
-- name    : GlobalTheory.DualCokernel.d_d_apply
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:06:44.696707+00:00
-- url     : https://prove2.me/theorems/b67c658c-ef61-4812-a35b-fdbbf83b16bb
-- title:
--   Dual Cokernel: d d apply
-- statement:
--   The Dual Cokernel construction uses the d d apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsSMulRegularCokerDualMapOfExactFibres.lean#L219-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsSMulRegularCokerDualMapOfExactFibres.lean#L219-L221

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
variable (C : CochainComplex (ModuleCat.{0} R) ℕ)

theorem GlobalTheory.DualCokernel.d_d_apply (i j k : ℕ) (x : C.X i) : (C.d j k).hom ((C.d i j).hom x) = 0 := by sorry
