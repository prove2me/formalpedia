-- Prove2me | Theorems.Thm_GlobalTheory_JR_HermInv_det_unit
-- name    : GlobalTheory.JR.HermInv.det_unit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:39:02.184823+00:00
-- url     : https://prove2.me/theorems/ccc1ad3d-c069-4b86-8f74-58161e53bb04
-- title:
--   Herm Inv: det unit
-- statement:
--   The Herm Inv construction uses the det unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActionHermitianInvariantsTransitive.lean#L294-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActionHermitianInvariantsTransitive.lean#L294-L300

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.HermInv
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
variable {r : ℕ}

theorem GlobalTheory.JR.HermInv.det_unit (a : Inv r F) (hΔ : Delta a ≠ 0) (h : Matrix (Fin r) (Fin r) E)
    (hh : hᴴ * h = (hankel a).map (algebraMap F E)) : IsUnit h.det := by sorry
