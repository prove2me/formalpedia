-- Prove2me | Theorems.Thm_GlobalTheory_TensorNormCompare_finiteDimensional_nablaSq
-- name    : GlobalTheory.TensorNormCompare.finiteDimensional_nablaSq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:42:27.225842+00:00
-- url     : https://prove2.me/theorems/59cf3415-277e-52d5-b3e2-f74046f94ca1
-- title:
--   Tensor Norm Compare: finite Dimensional nabla Sq
-- statement:
--   The Tensor Norm Compare construction uses the finite Dimensional nabla Sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TensorNormLeIffTensorNormBound.lean#L75-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TensorNormLeIffTensorNormBound.lean#L75-L80

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TensorPlaceNorm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TensorNormBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TensorNormLeIffTensorNormBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.TensorNormCompare
open Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.IndefiniteRowSideFullHecke
variable {ι : Type} [Fintype ι] {n n' : ℕ}

theorem GlobalTheory.TensorNormCompare.finiteDimensional_nablaSq (lam : DomWeight n) : FiniteDimensional ℂ (nablaSq ℂ n lam) := by sorry
