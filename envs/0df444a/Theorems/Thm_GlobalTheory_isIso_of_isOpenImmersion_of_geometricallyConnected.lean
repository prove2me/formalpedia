-- Prove2me | Theorems.Thm_GlobalTheory_isIso_of_isOpenImmersion_of_geometricallyConnected
-- name    : GlobalTheory.isIso_of_isOpenImmersion_of_geometricallyConnected
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:58:55.74482+00:00
-- url     : https://prove2.me/theorems/e3aa3742-817a-426a-bf11-36560563ecea
-- title:
--   Global Theory: is Iso of is Open Immersion of geometrically Connected
-- statement:
--   The Global Theory construction uses the is Iso of is Open Immersion of geometrically Connected property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsIsoOfIsOpenImmersionOfGeometricallyConnected.lean#L91-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsIsoOfIsOpenImmersionOfGeometricallyConnected.lean#L91-L121

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsIsoOfIsOpenImmersionOfGeometricallyConnected
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory

theorem GlobalTheory.isIso_of_isOpenImmersion_of_geometricallyConnected :
    ∀ (S : Scheme.{0}) (Ga G : Over S) [GrpObj Ga] [GrpObj G] (p : Ga ⟶ G), IsMonHom p →
      IsOpenImmersion p.left → LocallyOfFiniteType G.hom → GeometricallyConnected G.hom → IsIso p := by sorry
