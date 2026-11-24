-- Prove2me | Theorems.Thm_GlobalTheory_MatSqrtNearOne_tau_mul
-- name    : GlobalTheory.MatSqrtNearOne.tau_mul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:19:52.313483+00:00
-- url     : https://prove2.me/theorems/105acb48-5098-4b3f-b17f-ab42bdbc02d4
-- title:
--   Mat Sqrt Near One: tau mul
-- statement:
--   The Mat Sqrt Near One construction uses the tau mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMatrixSqrtNearOneUltrametric.lean#L77-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMatrixSqrtNearOneUltrametric.lean#L77-L79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMatrixSqrtNearOneUltrametric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open GlobalTheory GlobalTheory.MatSqrtNearOne
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K] {n : ℕ}

theorem GlobalTheory.MatSqrtNearOne.tau_mul (σ : K →+* K) (A B : Matrix (Fin n) (Fin n) K) :
    ((A * B).map σ)ᵀ = (B.map σ)ᵀ * (A.map σ)ᵀ := by sorry
