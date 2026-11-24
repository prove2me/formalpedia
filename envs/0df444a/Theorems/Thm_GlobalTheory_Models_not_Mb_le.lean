-- Prove2me | Theorems.Thm_GlobalTheory_Models_not_Mb_le
-- name    : GlobalTheory.Models.not_Mb_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:27:10.985932+00:00
-- url     : https://prove2.me/theorems/24a9ea20-9cf7-4fa0-817c-82c046049cd3
-- title:
--   Models: not Mb le
-- statement:
--   The Models construction uses the not Mb le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CoprimeLevel.lean#L117-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CoprimeLevel.lean#L117-L125

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_AuxiliaryInertOddPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CmGeneratorSqQuadraticEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CoprimeLevel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
open GlobalTheory GlobalTheory.Models
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.Models.not_Mb_le (H : Host E) {n : ℕ} (hn : AuxiliaryInertOddPrime H n) (l : Level H) (P : Ideal (𝓞 E)) (hP : P.IsPrime)
    (hnP : (n : 𝓞 E) ∈ P) : ¬ l.Mb ≤ P := by sorry
