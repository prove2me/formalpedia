-- Prove2me | Theorems.Thm_GlobalTheory_UTrans_CharDet_isU_refl
-- name    : GlobalTheory.UTrans.CharDet.isU_refl
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:46:48.785645+00:00
-- url     : https://prove2.me/theorems/c9a42bc7-da91-56a0-9a99-5cbf5bfbc775
-- title:
--   Char Det: is U refl
-- statement:
--   The Char Det construction uses the is U refl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CharEqOneOfDetEqOne.lean#L16-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CharEqOneOfDetEqOne.lean#L16-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TransvectionIdentitiesUnitary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryTransvectionSubmonoidNormalDetOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_QuasiReflectionEqUnitaryTransvectionMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryGeneratedByQuasiReflectionsAndWittStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryCharacterKillsUnitaryTransvectionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CharEqOneOfDetEqOne
import Theorems.Thm_GlobalTheory_UTrans_ReflChar0_isU_refl

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

theorem GlobalTheory.UTrans.CharDet.isU_refl (hG : IsHerm σ G) {x : Fin n → E} {u : E} (hx : hf σ G x x ≠ 0) (hu : u * σ u = 1) :
    IsU σ G (tv σ G x ((u - 1) / hf σ G x x)) := by sorry
