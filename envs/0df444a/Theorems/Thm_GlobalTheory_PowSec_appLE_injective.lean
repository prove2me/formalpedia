-- Prove2me | Theorems.Thm_GlobalTheory_PowSec_appLE_injective
-- name    : GlobalTheory.PowSec.appLE_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:42:48.787892+00:00
-- url     : https://prove2.me/theorems/e429fcb3-26ba-4557-a4e4-5aaedde64601
-- title:
--   Pow Sec: app LE injective
-- statement:
--   The Pow Sec construction uses the app LE injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsIndepSections.lean#L61-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsIndepSections.lean#L61-L65

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIndepSections
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.PowSec
variable {X Y : Scheme.{0}} (L : LB X) (σ : Y ⟶ X) (ρ : X ⟶ Y) (e : ρ ≫ σ = 𝟙 X) (n : ℤ)

theorem GlobalTheory.PowSec.appLE_injective [IsIso ρ] (U : Y.Opens) (V : X.Opens) (h : V = ρ ⁻¹ᵁ U) :
    Function.Injective (ρ.appLE U V h.le).hom := by sorry
