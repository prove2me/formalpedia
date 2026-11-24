-- Prove2me | Theorems.Thm_GlobalTheory_JR_HermInv_mulBm_eq
-- name    : GlobalTheory.JR.HermInv.mulBm_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:33:26.40274+00:00
-- url     : https://prove2.me/theorems/1993d054-036c-4a0c-8231-2083f7a1a4e5
-- title:
--   Herm Inv: mul Bm eq
-- statement:
--   The Herm Inv construction uses the mul Bm eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActionHermitianInvariantsTransitive.lean#L68-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActionHermitianInvariantsTransitive.lean#L68-L75

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

theorem GlobalTheory.JR.HermInv.mulBm_eq (Y : Gl r K) (k : ℕ) : Y.2.2.1 ᵥ* (Y.1 ^ k * Bm Y) = fun j : Fin r => mom Y (k + j) := by sorry
