-- Prove2me | Theorems.Thm_GlobalTheory_KeyPow_theta_sq_congr_mod_two
-- name    : GlobalTheory.KeyPow.theta_sq_congr_mod_two
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:50:09.564565+00:00
-- url     : https://prove2.me/theorems/f3837375-f719-419d-bb3e-86f838a816e9
-- title:
--   Key Pow: theta sq congr mod two
-- statement:
--   The Key Pow construction uses the theta sq congr mod two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ThetaSqCongrModTwo.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ThetaSqCongrModTwo.lean#L15-L18

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

theorem GlobalTheory.KeyPow.theta_sq_congr_mod_two {g : ℕ} {k k' m m' : Fin g → ℤ} (h : ∀ i, k i % 2 = m i % 2)
    (h' : ∀ i, k' i % 2 = m' i % 2) (z : Fin g → ℂ) (τ : Matrix (Fin g) (Fin g) ℂ) :
    theta (halfVec k) (halfVec k') z τ ^ 2 = theta (halfVec m) (halfVec m') z τ ^ 2 := by sorry
