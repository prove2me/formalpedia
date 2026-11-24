-- Prove2me | Theorems.Thm_GlobalTheory_Mem_Capelli_trAlg_shift_le
-- name    : GlobalTheory.Mem.Capelli.trAlg_shift_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:28:27.500067+00:00
-- url     : https://prove2.me/theorems/a0f70998-dae0-4750-bca0-7255cd239bda
-- title:
--   Capelli: tr Alg shift le
-- statement:
--   The Capelli construction uses the tr Alg shift le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AdjoinGelfandInvariantsDualPairEq.lean#L22-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AdjoinGelfandInvariantsDualPairEq.lean#L22-L32

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

theorem GlobalTheory.Mem.Capelli.trAlg_shift_le (M : Matrix (Fin n) (Fin n) A) (s c : ℂ) : trAlg (s • M + c • 1) ≤ trAlg M := by sorry
