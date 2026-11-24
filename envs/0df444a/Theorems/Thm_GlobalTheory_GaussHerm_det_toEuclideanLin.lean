-- Prove2me | Theorems.Thm_GlobalTheory_GaussHerm_det_toEuclideanLin
-- name    : GlobalTheory.GaussHerm.det_toEuclideanLin
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:51:04.825829+00:00
-- url     : https://prove2.me/theorems/5d6e8156-c780-462e-9956-dfa5d467c6ed
-- title:
--   Gauss Herm: det to Euclidean Lin
-- statement:
--   The Gauss Herm construction uses the det to Euclidean Lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralExpNegHermitianFormPosDef.lean#L12-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralExpNegHermitianFormPosDef.lean#L12-L19

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralExpNegHermitianFormPosDef
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder
open GlobalTheory GlobalTheory.GaussHerm

theorem GlobalTheory.GaussHerm.det_toEuclideanLin {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ) :
    LinearMap.det (Matrix.toEuclideanLin C) = C.det := by sorry
