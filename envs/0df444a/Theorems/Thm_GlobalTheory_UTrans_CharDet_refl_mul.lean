-- Prove2me | Theorems.Thm_GlobalTheory_UTrans_CharDet_refl_mul
-- name    : GlobalTheory.UTrans.CharDet.refl_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T02:54:15.593034+00:00
-- url     : https://prove2.me/theorems/830d2dc2-2ca3-5547-9586-8911ca2992dc
-- title:
--   Char Det: refl mul
-- statement:
--   The Char Det construction uses the refl mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CharEqOneOfDetEqOne.lean#L23-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CharEqOneOfDetEqOne.lean#L23-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TransvectionIdentitiesUnitary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryTransvectionSubmonoidNormalDetOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_QuasiReflectionEqUnitaryTransvectionMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryGeneratedByQuasiReflectionsAndWittStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryCharacterKillsUnitaryTransvectionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CharEqOneOfDetEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open GlobalTheory GlobalTheory.UTrans GlobalTheory.UTrans.CharDet
variable {E : Type} [Field E] {n : ℕ} {σ : E →+* E} {G : Matrix (Fin n) (Fin n) E}

theorem GlobalTheory.UTrans.CharDet.refl_mul {x : Fin n → E} (u v : E) (hx : hf σ G x x ≠ 0) :
    tv σ G x ((u - 1) / hf σ G x x) * tv σ G x ((v - 1) / hf σ G x x) =
      tv σ G x ((u * v - 1) / hf σ G x x) := by sorry
