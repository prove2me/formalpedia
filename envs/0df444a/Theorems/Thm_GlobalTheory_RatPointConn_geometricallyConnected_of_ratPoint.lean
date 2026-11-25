-- Prove2me | Theorems.Thm_GlobalTheory_RatPointConn_geometricallyConnected_of_ratPoint
-- name    : GlobalTheory.RatPointConn.geometricallyConnected_of_ratPoint
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:20:23.365003+00:00
-- url     : https://prove2.me/theorems/594f66dc-88be-4837-8d79-f6a17df66311
-- title:
--   Rat Point Conn: geometrically Connected of rat Point
-- statement:
--   The Rat Point Conn construction uses the geometrically Connected of rat Point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GeometricallyConnectedOfRatPoint.lean#L122-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GeometricallyConnectedOfRatPoint.lean#L122-L125

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GeometricallyConnectedOfRatPoint
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory GlobalTheory.RatPointConn
universe u

theorem GlobalTheory.RatPointConn.geometricallyConnected_of_ratPoint :
    ∀ (k : Type) [Field k] (X : Over (Sp k)), LocallyOfFiniteType X.hom → QuasiCompact X.hom → ConnectedSpace X.left → Nonempty (𝟙_ (Over (Sp k)) ⟶ X) → GeometricallyConnected X.hom := by sorry
