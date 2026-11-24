-- Prove2me | Theorems.Thm_GlobalTheory_Models_bar_mem_of_mem
-- name    : GlobalTheory.Models.bar_mem_of_mem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:27:11.717459+00:00
-- url     : https://prove2.me/theorems/951c2474-5612-49de-bcf9-558d07f7df65
-- title:
--   Models: bar mem of mem
-- statement:
--   The Models construction uses the bar mem of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CoprimeLevel.lean#L63-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CoprimeLevel.lean#L63-L115

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

theorem GlobalTheory.Models.bar_mem_of_mem (H : Host E) {n : ℕ} (hn : AuxiliaryInertOddPrime H n) (P : Ideal (𝓞 E)) (hP : P.IsPrime)
    (hnP : (n : 𝓞 E) ∈ P) {a : 𝓞 E} (ha : a ∈ Algebra.adjoin ℤ {H.w0}) (haP : a ∈ P) : H.bar a ∈ P := by sorry
