-- Prove2me | Theorems.Thm_GlobalTheory_Mem_Capelli_comm_one
-- name    : GlobalTheory.Mem.Capelli.comm_one
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:29:07.645675+00:00
-- url     : https://prove2.me/theorems/b7d6bf2f-b4e8-4823-a760-cb8203618f74
-- title:
--   Capelli: comm one
-- statement:
--   The Capelli construction uses the comm one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AdjoinGelfandInvariantsDualPairEq.lean#L56-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AdjoinGelfandInvariantsDualPairEq.lean#L56-L61

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

theorem GlobalTheory.Mem.Capelli.comm_one (a : Fin m) (l i j : Fin n) :
    D a l * (X * D) i j = (X * D) i j * D a l + if i = l then D a j else 0 := by sorry
