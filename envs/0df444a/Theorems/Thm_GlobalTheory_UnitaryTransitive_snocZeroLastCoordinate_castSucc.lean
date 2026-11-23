-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryTransitive_snocZeroLastCoordinate_castSucc
-- name    : GlobalTheory.UnitaryTransitive.snocZeroLastCoordinate_castSucc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:06:12.710803+00:00
-- url     : https://prove2.me/theorems/5b224e1f-f67a-4353-9ee0-5f33d7d5874f
-- title:
--   Unitary Transitive: snoc Zero Last Coordinate cast Succ
-- statement:
--   The Unitary Transitive construction uses the snoc Zero Last Coordinate cast Succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntegralUnitaryGroupTransitiveNormOneVectors.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntegralUnitaryGroupTransitiveNormOneVectors.lean#L15-L16

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
variable {E : Type} [NormedField E] [StarRing E]

theorem GlobalTheory.UnitaryTransitive.snocZeroLastCoordinate_castSucc {r : ℕ} (x : Fin r → E) (j : Fin r) : ext0 x j.castSucc = x j := by sorry
