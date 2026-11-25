-- Prove2me | Theorems.Thm_GlobalTheory_ThetaPow_thTerm_blocks
-- name    : GlobalTheory.ThetaPow.thTerm_blocks
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T17:32:05.464817+00:00
-- url     : https://prove2.me/theorems/f05c4d3f-735e-5e53-bb3e-54c49767e0aa
-- title:
--   Theta Pow: th Term blocks
-- statement:
--   The Theta Pow construction uses the th Term blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ThetaCharBlockDiagonal.lean#L61-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ThetaCharBlockDiagonal.lean#L61-L72

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

theorem GlobalTheory.ThetaPow.thTerm_blocks (e : Fin j × Fin g ≃ Fin G) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℝ)
    (z : Fin G → ℂ) (m : Fin G → ℤ) :
    CanTh.thTerm (Matrix.of fun p q => if (e.symm p).1 = (e.symm q).1 then
        τ (e.symm p).2 (e.symm q).2 else 0) (fun p => a (e.symm p).2) (fun p => b (e.symm p).2) z m =
      ∏ i : Fin j, CanTh.thTerm τ a b (fun k => z (e (i, k))) (blockEquiv e m i) := by sorry
