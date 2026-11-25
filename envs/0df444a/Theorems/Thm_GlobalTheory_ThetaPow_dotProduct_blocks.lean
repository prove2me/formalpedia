-- Prove2me | Theorems.Thm_GlobalTheory_ThetaPow_dotProduct_blocks
-- name    : GlobalTheory.ThetaPow.dotProduct_blocks
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T17:17:31.98048+00:00
-- url     : https://prove2.me/theorems/028ee083-bbca-43bd-ba56-e20d7b1e1f8e
-- title:
--   Theta Pow: dot Product blocks
-- statement:
--   The Theta Pow construction uses the dot Product blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ThetaCharBlockDiagonal.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ThetaCharBlockDiagonal.lean#L16-L19

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_HasSumPolyDerivMulProdAddMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ThetaCharBlockDiagonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ThetaPow
variable {j g G : ℕ}

theorem GlobalTheory.ThetaPow.dotProduct_blocks {R : Type*} [CommRing R] (e : Fin j × Fin g ≃ Fin G) (x y : Fin G → R) :
    x ⬝ᵥ y = ∑ i : Fin j, (fun k => x (e (i, k))) ⬝ᵥ (fun k => y (e (i, k))) := by sorry
