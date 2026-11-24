-- Prove2me | Theorems.Thm_GlobalTheory_Mem_Capelli_trace_rec
-- name    : GlobalTheory.Mem.Capelli.trace_rec
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:29:10.91786+00:00
-- url     : https://prove2.me/theorems/9d1ed1cf-fd10-4dd6-a8cd-7f2ae7da9df2
-- title:
--   Capelli: trace rec
-- statement:
--   The Capelli construction uses the trace rec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AdjoinGelfandInvariantsDualPairEq.lean#L87-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AdjoinGelfandInvariantsDualPairEq.lean#L87-L120

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PolarConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommuteGelfandInvariantMatrixUnitsOfGlRel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AdjoinGelfandInvariantsDualPairEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.Mem.Lift
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Capelli
variable {A : Type} [Ring A] [Algebra ℂ A] {n m : ℕ}
variable (X : Matrix (Fin n) (Fin m) A) (D : Matrix (Fin m) (Fin n) A)
  (hdd : ∀ a l b j, D a l * D b j = D b j * D a l)
  (hdx : ∀ a l i b, D a l * X i b = X i b * D a l + if i = l ∧ b = a then 1 else 0)
omit [Algebra ℂ A]
include hdd hdx

theorem GlobalTheory.Mem.Capelli.trace_rec (p : ℕ) :
    ((D * X) ^ (p + 1)).trace = ((X * D) ^ (p + 1)).trace + (m : A) * ((X * D) ^ p).trace
      + ∑ r ∈ Finset.range p, ((X * D) ^ r).trace * ((D * X) ^ (p - (r + 1) + 1)).trace := by sorry
