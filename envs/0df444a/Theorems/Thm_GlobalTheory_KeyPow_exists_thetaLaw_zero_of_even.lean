-- Prove2me | Theorems.Thm_GlobalTheory_KeyPow_exists_thetaLaw_zero_of_even
-- name    : GlobalTheory.KeyPow.exists_thetaLaw_zero_of_even
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:03:48.753077+00:00
-- url     : https://prove2.me/theorems/cf39f1ee-e738-43fe-b72a-6651f76b7e7c
-- title:
--   Key Pow: exists theta Law zero of even
-- statement:
--   The Key Pow construction uses the exists theta Law zero of even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsThetaLawZeroOfEven.lean#L15-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsThetaLawZeroOfEven.lean#L15-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ThetaSqCongrModTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ThetaLawMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsIsSymmMulVecAddDiagModTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsThetaLawZeroOfEven
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.KeyPow
open Matrix ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

theorem GlobalTheory.KeyPow.exists_thetaLaw_zero_of_even (hInv : ReciprocityTheory.ChartRestriction.G.Key.Chi.InversionStatement) (g : ℕ)
    (n n' : Fin g → ℤ) (h : Even (n ⬝ᵥ n')) :
    ∃ sp ∈ Matrix.symplecticGroup (Fin g) ℤ, GlobalTheory.KeyPow.ThetaLaw g sp n n' 0 0 := by sorry
