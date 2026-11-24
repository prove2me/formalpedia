-- Prove2me | Theorems.Thm_GlobalTheory_PowSec_appLE_bijective
-- name    : GlobalTheory.PowSec.appLE_bijective
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:52:50.334361+00:00
-- url     : https://prove2.me/theorems/08a65951-b2e3-4dfd-b901-44fd0704b418
-- title:
--   Pow Sec: app LE bijective
-- statement:
--   The Pow Sec construction uses the app LE bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsBasisOfIsField.lean#L18-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsBasisOfIsField.lean#L18-L22

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIndepSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsBasisOfIsField
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

theorem GlobalTheory.PowSec.appLE_bijective [IsIso ρ] (U : Y.Opens) (V : X.Opens) (h : V = ρ ⁻¹ᵁ U) :
    Function.Bijective (ρ.appLE U V h.le).hom := by sorry
