-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryTransitive_uO_transitive
-- name    : GlobalTheory.UnitaryTransitive.uO_transitive
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:45:13.3395+00:00
-- url     : https://prove2.me/theorems/beb2a322-514b-4565-91cd-8562c149dbe7
-- title:
--   Unitary Transitive: u O transitive
-- statement:
--   The Unitary Transitive construction uses the u O transitive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntegralUnitaryGroupTransitiveNormOneVectors.lean#L144-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntegralUnitaryGroupTransitiveNormOneVectors.lean#L144-L173

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnimodularHermitianMatrixCongruentOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegralUnitaryGroupTransitiveNormOneVectors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.UnitaryTransitive

theorem GlobalTheory.UnitaryTransitive.uO_transitive : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (v : Fin (r + 1) → E), (∀ i, ‖v i‖ ≤ 1) → star v ⬝ᵥ v = 1 →
    ∃ k ∈ uO (r + 1) E, k.1 *ᵥ Pi.single (Fin.last r) 1 = v := by sorry
