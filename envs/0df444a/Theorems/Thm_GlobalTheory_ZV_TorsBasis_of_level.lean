-- Prove2me | Theorems.Thm_GlobalTheory_ZV_TorsBasis_of_level
-- name    : GlobalTheory.ZV.TorsBasis.of_level
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:44:58.718108+00:00
-- url     : https://prove2.me/theorems/70e4a28c-c305-5bb8-81ce-cccd30dede24
-- title:
--   Tors Basis: of level
-- statement:
--   The Tors Basis construction uses the of level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ModuliSpaces/SectionsHaveFiniteDimension.lean#L223-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ModuliSpaces/SectionsHaveFiniteDimension.lean#L223-L237

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_SectionsHaveFiniteDimension
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
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.ZV
variable {K : Type} [Field K] {X Y : Scheme.{0}}

theorem GlobalTheory.ZV.TorsBasis.of_level [IsAlgClosed K] (P : Out.PolAV (Sp K)) {k : ℕ} (hk : 0 < k) {ze : Γ(Sp K, ⊤)ˣ}
    (lev : Out.Level P k ze) : TorsBasis P.A k lev.pt := by sorry
