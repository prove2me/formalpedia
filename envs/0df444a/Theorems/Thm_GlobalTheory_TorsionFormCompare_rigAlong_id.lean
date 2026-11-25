-- Prove2me | Theorems.Thm_GlobalTheory_TorsionFormCompare_rigAlong_id
-- name    : GlobalTheory.TorsionFormCompare.rigAlong_id
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:42:27.49009+00:00
-- url     : https://prove2.me/theorems/202ff58c-7d1e-5501-8352-5eeda60abb31
-- title:
--   Torsion Form Compare: rig Along id
-- statement:
--   The Torsion Form Compare construction uses the rig Along id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SameUnifRefl.lean#L42-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SameUnifRefl.lean#L42-L47

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_OLinBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleIdentityIso
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SameUnifRefl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TorsionFormCompare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
variable {R : Type} [CommRing R] [IsDomain R]

theorem GlobalTheory.TorsionFormCompare.rigAlong_id {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (L : RigLB G) :
    RigAlong (𝟙 G) L L (isoPullId (idIso L.L) rfl) := by sorry
