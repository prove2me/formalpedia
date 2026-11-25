-- Prove2me | Theorems.Thm_GlobalTheory_HeckeFrCompare_ext_of_points
-- name    : GlobalTheory.HeckeFrCompare.ext_of_points
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:45:58.778813+00:00
-- url     : https://prove2.me/theorems/5dbef67b-c398-44c4-ab5c-2ab957ffdba7
-- title:
--   Hecke Fr Compare: ext of points
-- statement:
--   The Hecke Fr Compare construction uses the ext of points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HkRelFrOfTransportIff.lean#L15-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HkRelFrOfTransportIff.lean#L15-L24

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_HeckeFr
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_FibrePushforward
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HkRelFrOfTransportIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HeckeFrCompare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.HeckeFrCompare.ext_of_points {Ω : Type} [Field Ω] [IsAlgClosed Ω] {T Y Z : Scheme.{0}} (t : T ⟶ Sp Ω)
    [LocallyOfFiniteType t] [IsReduced T] (s : Y ⟶ Z) [IsSeparated s] {f g : T ⟶ Y} (H' : f ≫ s = g ≫ s)
    (Hq : ∀ q : Sp Ω ⟶ T, q ≫ t = 𝟙 _ → q ≫ f = q ≫ g) : f = g := by sorry
