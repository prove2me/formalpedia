-- Prove2me | Theorems.Thm_GlobalTheory_thetaChar_blockDiagonal
-- name    : GlobalTheory.thetaChar_blockDiagonal
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T17:21:21.859376+00:00
-- url     : https://prove2.me/theorems/2cc74a6f-78c4-43d2-a3dc-1a0749aae9bc
-- title:
--   Global Theory: theta Char block Diagonal
-- statement:
--   The Global Theory construction uses the theta Char block Diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ThetaCharBlockDiagonal.lean#L80-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ThetaCharBlockDiagonal.lean#L80-L103

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
open GlobalTheory
open ThetaPow

theorem GlobalTheory.thetaChar_blockDiagonal (j g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℝ) (G : ℕ)
    (e : Fin j × Fin g ≃ Fin G) (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef) :
    let τ' : Matrix (Fin G) (Fin G) ℂ := Matrix.of fun p q =>
      if (e.symm p).1 = (e.symm q).1 then τ (e.symm p).2 (e.symm q).2 else 0
    τ'.IsSymm ∧ (τ'.map Complex.im).PosDef ∧ ∀ z : Fin G → ℂ,
      thetaChar τ' (fun p => (a (e.symm p).2 : ℂ)) (fun p => (b (e.symm p).2 : ℂ)) z =
        ∏ i : Fin j, thetaChar τ (fun k => (a k : ℂ)) (fun k => (b k : ℂ)) (fun k => z (e (i, k))) := by sorry
