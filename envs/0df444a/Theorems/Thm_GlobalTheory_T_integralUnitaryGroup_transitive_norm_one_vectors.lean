-- Prove2me | Theorems.Thm_GlobalTheory_T_integralUnitaryGroup_transitive_norm_one_vectors
-- name    : GlobalTheory.T.integralUnitaryGroup_transitive_norm_one_vectors
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:47:06.910871+00:00
-- url     : https://prove2.me/theorems/6e429b41-18bf-4280-a4e8-c366f5c030f1
-- title:
--   T: integral Unitary Group transitive norm one vectors
-- statement:
--   The T construction uses the integral Unitary Group transitive norm one vectors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntegralUnitaryGroupTransitiveNormOneVectorsStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntegralUnitaryGroupTransitiveNormOneVectorsStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegralUnitaryGroupTransitiveNormOneVectors
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegralUnitaryGroupTransitiveNormOneVectorsStatement
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

theorem GlobalTheory.T.integralUnitaryGroup_transitive_norm_one_vectors : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (v : Fin (r + 1) → E), (∀ i, ‖v i‖ ≤ 1) → star v ⬝ᵥ v = 1 → ∃ k ∈ uO (r + 1) E, k.1 *ᵥ Pi.single (Fin.last r) 1 = v := by sorry
