-- Prove2me | Theorems.Thm_GlobalTheory_JR_LinDesc_tm_isClosedEmbedding
-- name    : GlobalTheory.JR.LinDesc.tm_isClosedEmbedding
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:34:23.822494+00:00
-- url     : https://prove2.me/theorems/b4c639bb-f25e-4dfd-83dd-3597956951b2
-- title:
--   Lin Desc: tm is Closed Embedding
-- statement:
--   The Lin Desc construction uses the tm is Closed Embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsClosedEmbeddingLeftMulMatrixPowerBasisUnitsHom.lean#L6-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsClosedEmbeddingLeftMulMatrixPowerBasisUnitsHom.lean#L6-L54

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LeftMulTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsClosedEmbeddingLeftMulMatrixPowerBasisUnitsHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.LinDesc

theorem GlobalTheory.JR.LinDesc.tm_isClosedEmbedding : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p), Topology.IsClosedEmbedding (LinDesc.tm A hG) := by sorry
