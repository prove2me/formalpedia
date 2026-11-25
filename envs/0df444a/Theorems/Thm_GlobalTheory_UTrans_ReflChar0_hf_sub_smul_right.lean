-- Prove2me | Theorems.Thm_GlobalTheory_UTrans_ReflChar0_hf_sub_smul_right
-- name    : GlobalTheory.UTrans.ReflChar0.hf_sub_smul_right
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T01:29:46.937116+00:00
-- url     : https://prove2.me/theorems/ed27785a-5a4c-49ab-86a9-e708f15de5e6
-- title:
--   Refl Char0: hf sub smul right
-- statement:
--   The Refl Char0 construction uses the hf sub smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnitaryGeneratedByQuasiReflectionsAndWitt.lean#L19-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnitaryGeneratedByQuasiReflectionsAndWitt.lean#L19-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TransvectionIdentitiesUnitary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryGeneratedByQuasiReflectionsAndWitt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open GlobalTheory GlobalTheory.UTrans GlobalTheory.UTrans.ReflChar0
open GlobalTheory.UTrans.Calc
variable {E : Type} [Field E] {n : ℕ} {σ : E →+* E} {G : Matrix (Fin n) (Fin n) E}

theorem GlobalTheory.UTrans.ReflChar0.hf_sub_smul_right (z x w : Fin n → E) (e : E) :
    hf σ G w (z - e • x) = hf σ G w z - σ e * hf σ G w x := by sorry
