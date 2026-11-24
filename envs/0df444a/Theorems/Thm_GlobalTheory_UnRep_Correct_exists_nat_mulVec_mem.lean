-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_Correct_exists_nat_mulVec_mem
-- name    : GlobalTheory.UnRep.Correct.exists_nat_mulVec_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:24:35.926792+00:00
-- url     : https://prove2.me/theorems/b6cb6d88-1318-440e-b317-be9dcd01b896
-- title:
--   Correct: exists nat mul Vec mem
-- statement:
--   The Correct construction uses the exists nat mul Vec mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUnitaryCorrectionCongruentOneAtLevel.lean#L27-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUnitaryCorrectionCongruentOneAtLevel.lean#L27-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsNormOneReflectionCorrectionAtLevelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryMatrixEqProdQuasiReflectionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryQuasiReflectionLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsNsmulMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitaryCorrectionCongruentOneAtLevel
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

theorem GlobalTheory.UnRep.Correct.exists_nat_mulVec_mem [NumberField E] (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (M : Matrix (Fin n) (Fin n) E) :
    ∃ d : ℕ, 0 < d ∧ ∀ v ∈ L, d • (M *ᵥ v) ∈ L := by sorry
