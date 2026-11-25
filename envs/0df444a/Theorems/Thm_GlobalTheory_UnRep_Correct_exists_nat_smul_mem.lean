-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_Correct_exists_nat_smul_mem
-- name    : GlobalTheory.UnRep.Correct.exists_nat_smul_mem
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:43:31.87739+00:00
-- url     : https://prove2.me/theorems/b92da7ce-a54e-4dad-ae73-a6979247ff92
-- title:
--   Correct: exists nat smul mem
-- statement:
--   The Correct construction uses the exists nat smul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUnitaryCorrectionCongruentOneAtLevel.lean#L16-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUnitaryCorrectionCongruentOneAtLevel.lean#L16-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsNormOneReflectionCorrectionAtLevelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryMatrixEqProdQuasiReflectionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryQuasiReflectionLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsNsmulMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitaryCorrectionCongruentOneAtLevel
import Theorems.Thm_GlobalTheory_NatMulIntegral_exists_nat_smul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.Correct
variable {E : Type} [Field E] {n : ℕ}

theorem GlobalTheory.UnRep.Correct.exists_nat_smul_mem [NumberField E] (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∃ d : ℕ, 0 < d ∧ d • x ∈ L := by sorry
