-- Prove2me | Theorems.Thm_GlobalTheory_JR_HermInv_unit_conj_pow
-- name    : GlobalTheory.JR.HermInv.unit_conj_pow
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:33:06.106451+00:00
-- url     : https://prove2.me/theorems/9512db8c-11da-4c8d-9454-f92030a545e4
-- title:
--   Herm Inv: unit conj pow
-- statement:
--   The Herm Inv construction uses the unit conj pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActionHermitianInvariantsTransitive.lean#L196-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActionHermitianInvariantsTransitive.lean#L196-L203

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

theorem GlobalTheory.JR.HermInv.unit_conj_pow (g : Matrix.unitaryGroup (Fin r) E) (A : Matrix (Fin r) (Fin r) E) (k : ℕ) :
    (g.1 * A * star g.1) ^ k = g.1 * A ^ k * star g.1 := by sorry
