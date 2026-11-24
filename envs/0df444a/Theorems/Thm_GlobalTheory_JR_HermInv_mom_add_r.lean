-- Prove2me | Theorems.Thm_GlobalTheory_JR_HermInv_mom_add_r
-- name    : GlobalTheory.JR.HermInv.mom_add_r
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:38:50.399684+00:00
-- url     : https://prove2.me/theorems/167c3222-6a75-4430-ba79-a7500b15138d
-- title:
--   Herm Inv: mom add r
-- statement:
--   The Herm Inv construction uses the mom add r property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActionHermitianInvariantsTransitive.lean#L77-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActionHermitianInvariantsTransitive.lean#L77-L80

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

theorem GlobalTheory.JR.HermInv.mom_add_r (Y : Gl r K) (q : Fin r → K) (hq : Y.1 ^ r *ᵥ Y.2.1 = -(Bm Y *ᵥ q)) (k : ℕ) :
    mom Y (k + r) = -((fun j : Fin r => mom Y (k + j)) ⬝ᵥ q) := by sorry
