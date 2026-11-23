-- Prove2me | Theorems.Thm_GlobalTheory_PerfectPairingCount_linearIndependent_unitsChar
-- name    : GlobalTheory.PerfectPairingCount.linearIndependent_unitsChar
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:51:31.095307+00:00
-- url     : https://prove2.me/theorems/1eef8790-1fe6-476f-8b80-45670ee67f72
-- title:
--   Perfect Pairing Count: linear Independent units Char
-- statement:
--   The Perfect Pairing Count construction uses the linear Independent units Char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PerfectPairingOrthogonalOfCard.lean#L15-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PerfectPairingOrthogonalOfCard.lean#L15-L22

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PerfectPairingOrthogonalOfCard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PerfectPairingCount
variable {F : Type} [Field F]

theorem GlobalTheory.PerfectPairingCount.linearIndependent_unitsChar (G : Type) [Group G] :
    LinearIndependent F (fun (f : G →* Fˣ) => (fun g => ((f g : Fˣ) : F) : G → F)) := by sorry
