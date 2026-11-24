-- Prove2me | Theorems.Thm_GlobalTheory_JR_HermInv_mul_Bm
-- name    : GlobalTheory.JR.HermInv.mul_Bm
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:33:28.83957+00:00
-- url     : https://prove2.me/theorems/3da305d3-1365-4d29-ab35-a313cee80c0e
-- title:
--   Herm Inv: mul Bm
-- statement:
--   The Herm Inv construction uses the mul Bm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActionHermitianInvariantsTransitive.lean#L231-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActionHermitianInvariantsTransitive.lean#L231-L246

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

theorem GlobalTheory.JR.HermInv.mul_Bm (Y : Gl r K) (q : Fin r → K) (hq : Y.1 ^ r *ᵥ Y.2.1 = -(Bm Y *ᵥ q)) :
    Y.1 * Bm Y = Bm Y * companion q := by sorry
