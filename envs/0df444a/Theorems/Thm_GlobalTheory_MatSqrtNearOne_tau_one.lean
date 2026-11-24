-- Prove2me | Theorems.Thm_GlobalTheory_MatSqrtNearOne_tau_one
-- name    : GlobalTheory.MatSqrtNearOne.tau_one
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:19:57.670721+00:00
-- url     : https://prove2.me/theorems/c9ef704f-9556-4141-8bbe-7e62e7fec616
-- title:
--   Mat Sqrt Near One: tau one
-- statement:
--   The Mat Sqrt Near One construction uses the tau one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMatrixSqrtNearOneUltrametric.lean#L81-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMatrixSqrtNearOneUltrametric.lean#L81-L82

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

theorem GlobalTheory.MatSqrtNearOne.tau_one (σ : K →+* K) : ((1 : Matrix (Fin n) (Fin n) K).map σ)ᵀ = 1 := by sorry
