-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_PreUniformization_Ph_unique
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.PreUniformization.Ph.unique
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:18:43.30427+00:00
-- url     : https://prove2.me/theorems/9f3408d2-0108-431a-bf32-3763d348ce77
-- title:
--   Ph: unique
-- statement:
--   The Ph construction uses the unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/PreUniformization.lean#L180-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/PreUniformization.lean#L180-L189

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_PreUniformization
import Theorems.Thm_GlobalTheory_UU_CubWeil_unique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.PreUniformization
variable {R : Type} [CommRing R] [IsDomain R]
variable (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem GlobalTheory.IndefiniteRowSideFullHecke.PreUniformization.Ph.unique {k : ℕ} {y : D.X} {g : GtPtF D F} {w} {s s₁ s₂ : RawFam D F k} (h₁ : Ph D F k y g w s s₁)
    (h₂ : Ph D F k y g w s s₂) : s₁ = s₂ := by sorry
