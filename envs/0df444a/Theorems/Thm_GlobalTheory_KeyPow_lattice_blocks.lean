-- Prove2me | Theorems.Thm_GlobalTheory_KeyPow_lattice_blocks
-- name    : GlobalTheory.KeyPow.lattice_blocks
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T17:27:29.557373+00:00
-- url     : https://prove2.me/theorems/eda2ee4d-439b-50fc-84d8-5481a4f726a6
-- title:
--   Key Pow: lattice blocks
-- statement:
--   The Key Pow construction uses the lattice blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/LatticeBlocks.lean#L30-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/LatticeBlocks.lean#L30-L48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ThetaCharBlockDiagonal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsHolomorphicUniformisationPowerThetaKeyDatuStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_LatticeBlocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.KeyPow

theorem GlobalTheory.KeyPow.lattice_blocks {j g G : ℕ} (e : Fin j × Fin g ≃ Fin G) (τ : Matrix (Fin g) (Fin g) ℂ) (z : Fin G → ℂ) :
    (∀ i, ∃ m n : Fin g → ℤ, (fun k => z (e (i, k))) = (fun k => (m k : ℂ)) + τ.mulVec (fun k => (n k : ℂ))) ↔
      ∃ m n : Fin G → ℤ, z = (fun p => (m p : ℂ)) +
        (Matrix.of fun p q => if (e.symm p).1 = (e.symm q).1 then
          τ (e.symm p).2 (e.symm q).2 else 0 : Matrix (Fin G) (Fin G) ℂ).mulVec (fun p => (n p : ℂ)) := by sorry
