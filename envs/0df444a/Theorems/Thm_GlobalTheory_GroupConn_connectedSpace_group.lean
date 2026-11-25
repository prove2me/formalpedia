-- Prove2me | Theorems.Thm_GlobalTheory_GroupConn_connectedSpace_group
-- name    : GlobalTheory.GroupConn.connectedSpace_group
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:36:37.006525+00:00
-- url     : https://prove2.me/theorems/1fc0340c-f910-54bb-89e5-950d2079f3a9
-- title:
--   Group Conn: connected Space group
-- statement:
--   The Group Conn construction uses the connected Space group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ConnectedSpaceOfSection.lean#L39-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ConnectedSpaceOfSection.lean#L39-L47

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ConnectedSpaceOfSection
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
open GlobalTheory GlobalTheory.GroupConn

theorem GlobalTheory.GroupConn.connectedSpace_group : ∀ (S : Scheme.{0}) [ConnectedSpace S] (G : Over S) [GrpObj G] [Smooth G.hom] [GeometricallyConnected G.hom], ConnectedSpace G.left ∧ ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] (Y : Over S), ConnectedSpace Y.left → ConnectedSpace (splitTorus S X ⊗ Y).left ∧ ConnectedSpace (G ⊗ Y).left := by sorry
