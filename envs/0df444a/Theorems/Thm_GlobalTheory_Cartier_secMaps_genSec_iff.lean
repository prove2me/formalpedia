-- Prove2me | Theorems.Thm_GlobalTheory_Cartier_secMaps_genSec_iff
-- name    : GlobalTheory.Cartier.secMaps_genSec_iff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:58:41.094355+00:00
-- url     : https://prove2.me/theorems/6636728a-0f7c-4aae-916f-3510f0ff303e
-- title:
--   Cartier: sec Maps gen Sec iff
-- statement:
--   The Cartier construction uses the sec Maps gen Sec iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/IsRegularFnIffOfIsAffineOpen.lean#L226-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/IsRegularFnIffOfIsAffineOpen.lean#L226-L230

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
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
open GlobalTheory GlobalTheory.Cartier
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X Y Z : Scheme.{0}}

theorem GlobalTheory.Cartier.secMaps_genSec_iff {A B : LB X} (w : LB.Iso A B) (a : A.Gen) (ha : a.IsGen) (b : B.Gen)
    (hb : b.IsGen) :
    SecMaps w ⟨fun i => (a.s i).val, fun i j => congrArg Units.val (ha i j)⟩
      ⟨fun i => (b.s i).val, fun i j => congrArg Units.val (hb i j)⟩ ↔ LB.Gen.Maps w a b := by sorry
