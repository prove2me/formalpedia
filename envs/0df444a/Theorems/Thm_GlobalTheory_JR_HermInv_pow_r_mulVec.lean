-- Prove2me | Theorems.Thm_GlobalTheory_JR_HermInv_pow_r_mulVec
-- name    : GlobalTheory.JR.HermInv.pow_r_mulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:38:21.768711+00:00
-- url     : https://prove2.me/theorems/c89e9604-c9c8-4014-9725-257f6a8a58a7
-- title:
--   Herm Inv: pow r mul Vec
-- statement:
--   The Herm Inv construction uses the pow r mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActionHermitianInvariantsTransitive.lean#L50-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActionHermitianInvariantsTransitive.lean#L50-L66

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
variable {r : ℕ} {K : Type} [CommRing K]

theorem GlobalTheory.JR.HermInv.pow_r_mulVec [Nontrivial K] (Y : Gl r K) :
    Y.1 ^ r *ᵥ Y.2.1 = -(Bm Y *ᵥ fun i : Fin r => Y.1.charpoly.coeff i) := by sorry
