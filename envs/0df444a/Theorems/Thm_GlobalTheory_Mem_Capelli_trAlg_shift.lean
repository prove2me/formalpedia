-- Prove2me | Theorems.Thm_GlobalTheory_Mem_Capelli_trAlg_shift
-- name    : GlobalTheory.Mem.Capelli.trAlg_shift
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:29:21.094042+00:00
-- url     : https://prove2.me/theorems/c9bb8cd8-c5ea-4eba-ae19-b955ce31a367
-- title:
--   Capelli: tr Alg shift
-- statement:
--   The Capelli construction uses the tr Alg shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AdjoinGelfandInvariantsDualPairEq.lean#L34-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AdjoinGelfandInvariantsDualPairEq.lean#L34-L38

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

theorem GlobalTheory.Mem.Capelli.trAlg_shift (M : Matrix (Fin n) (Fin n) A) {s : ℂ} (hs : s ≠ 0) (c : ℂ) :
    trAlg (s • M + c • 1) = trAlg M := by sorry
