-- Prove2me | Theorems.Thm_GlobalTheory_KeyPow_ThetaLaw_congr_target
-- name    : GlobalTheory.KeyPow.ThetaLaw.congr_target
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:49:40.724733+00:00
-- url     : https://prove2.me/theorems/c8cfed9b-3141-42e2-9a80-b90ebf5d0ef3
-- title:
--   Theta Law: congr target
-- statement:
--   The Theta Law construction uses the congr target property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ThetaSqCongrModTwo.lean#L20-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ThetaSqCongrModTwo.lean#L20-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OfRealVecHalfVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ThetaSqCongrModTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
open GlobalTheory GlobalTheory.KeyPow

theorem GlobalTheory.KeyPow.ThetaLaw.congr_target {g : ℕ} {sp : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    {n n' k k' m m' : Fin g → ℤ} (hl : ThetaLaw g sp n n' k k') (h : ∀ i, m i % 2 = k i % 2)
    (h' : ∀ i, m' i % 2 = k' i % 2) : ThetaLaw g sp n n' m m' := by sorry
