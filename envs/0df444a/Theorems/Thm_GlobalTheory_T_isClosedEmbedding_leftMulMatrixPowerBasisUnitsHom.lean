-- Prove2me | Theorems.Thm_GlobalTheory_T_isClosedEmbedding_leftMulMatrixPowerBasisUnitsHom
-- name    : GlobalTheory.T.isClosedEmbedding_leftMulMatrixPowerBasisUnitsHom
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:48:05.695724+00:00
-- url     : https://prove2.me/theorems/b024bde2-7e81-42db-be00-be0159fa9a4d
-- title:
--   T: is Closed Embedding left Mul Matrix Power Basis Units Hom
-- statement:
--   The T construction uses the is Closed Embedding left Mul Matrix Power Basis Units Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsClosedEmbeddingLeftMulMatrixPowerBasisUnitsHomStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsClosedEmbeddingLeftMulMatrixPowerBasisUnitsHomStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsClosedEmbeddingLeftMulMatrixPowerBasisUnitsHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LeftMulTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsClosedEmbeddingLeftMulMatrixPowerBasisUnitsHomStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isClosedEmbedding_leftMulMatrixPowerBasisUnitsHom : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p), Topology.IsClosedEmbedding (LinDesc.tm A hG) := by sorry
