-- Prove2me | Theorems.Thm_GlobalTheory_HkFactor_ext_of_geometricPoints
-- name    : GlobalTheory.HkFactor.ext_of_geometricPoints
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T15:08:31.659889+00:00
-- url     : https://prove2.me/theorems/21ed388f-c8d2-4b57-8759-ffd813a9d3b7
-- title:
--   Hk Factor: ext of geometric Points
-- statement:
--   The Hk Factor construction uses the ext of geometric Points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniqueFactorThroughEtaleIsogenyReduced.lean#L16-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniqueFactorThroughEtaleIsogenyReduced.lean#L16-L33

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_KerScheme
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatQuotientIsoOfSameKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueFactorThroughEtaleIsogenyReduced
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
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
open GlobalTheory GlobalTheory.HkFactor

theorem GlobalTheory.HkFactor.ext_of_geometricPoints {T X Z : Scheme.{0}} [IsReduced T] (q : X ⟶ Z) [IsSeparated q]
    (f g : T ⟶ X) (h : f ≫ q = g ≫ q)
    (H : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T), x ≫ f = x ≫ g) : f = g := by sorry
