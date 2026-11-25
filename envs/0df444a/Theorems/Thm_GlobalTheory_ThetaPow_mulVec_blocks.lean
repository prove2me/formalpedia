-- Prove2me | Theorems.Thm_GlobalTheory_ThetaPow_mulVec_blocks
-- name    : GlobalTheory.ThetaPow.mulVec_blocks
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T17:16:15.301388+00:00
-- url     : https://prove2.me/theorems/47d4b993-2bae-4bdb-99b6-9e19f143f06a
-- title:
--   Theta Pow: mul Vec blocks
-- statement:
--   The Theta Pow construction uses the mul Vec blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ThetaCharBlockDiagonal.lean#L21-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ThetaCharBlockDiagonal.lean#L21-L34

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

theorem GlobalTheory.ThetaPow.mulVec_blocks {R : Type*} [CommRing R] (e : Fin j × Fin g ≃ Fin G)
    (M : Matrix (Fin g) (Fin g) R) (y : Fin G → R) (i : Fin j) :
    (fun k => ((Matrix.of fun p q => if (e.symm p).1 = (e.symm q).1 then
        M (e.symm p).2 (e.symm q).2 else 0 : Matrix (Fin G) (Fin G) R) *ᵥ y) (e (i, k))) =
      M *ᵥ fun k => y (e (i, k)) := by sorry
