-- Prove2me | Theorems.Thm_GlobalTheory_JR_OrbProper_continuous_actU
-- name    : GlobalTheory.JR.OrbProper.continuous_actU
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:43.857319+00:00
-- url     : https://prove2.me/theorems/a664c76e-2e14-4460-b5f7-315bf57733f0
-- title:
--   Orb Proper: continuous act U
-- statement:
--   The Orb Proper construction uses the continuous act U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryOrbitProperOfInvertibleKrylovColumns.lean#L19-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryOrbitProperOfInvertibleKrylovColumns.lean#L19-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompanionMatrixOfCoeffsPowMulVecFirstBasisVector
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryOrbitProperOfInvertibleKrylovColumns
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.OrbProper
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E] {r : ℕ}

theorem GlobalTheory.JR.OrbProper.continuous_actU :
    Continuous (fun q : Matrix.unitaryGroup (Fin r) E × Hn r F E => actU q.1 q.2) := by sorry
