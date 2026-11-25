-- Prove2me | Theorems.Thm_GlobalTheory_UTrans_ReflChar0_hf_sub_smul_left
-- name    : GlobalTheory.UTrans.ReflChar0.hf_sub_smul_left
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:29:46.096352+00:00
-- url     : https://prove2.me/theorems/5720855a-0a4e-49f0-bfb9-872ce63c8d05
-- title:
--   Refl Char0: hf sub smul left
-- statement:
--   The Refl Char0 construction uses the hf sub smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnitaryGeneratedByQuasiReflectionsAndWitt.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnitaryGeneratedByQuasiReflectionsAndWitt.lean#L14-L17

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

theorem GlobalTheory.UTrans.ReflChar0.hf_sub_smul_left (z x w : Fin n → E) (e : E) :
    hf σ G (z - e • x) w = hf σ G z w - e * hf σ G x w := by sorry
