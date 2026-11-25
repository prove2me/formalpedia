-- Prove2me | Theorems.Thm_GlobalTheory_DescTheta_exists_nhds_nonvanishing
-- name    : GlobalTheory.DescTheta.exists_nhds_nonvanishing
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:33:24.255485+00:00
-- url     : https://prove2.me/theorems/f45c1101-11d9-5f12-a723-7540e6192f7a
-- title:
--   Desc Theta: exists nhds nonvanishing
-- statement:
--   The Desc Theta construction uses the exists nhds nonvanishing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSecOnNonvanishingOfTameQuotient.lean#L96-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSecOnNonvanishingOfTameQuotient.lean#L96-L120

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSumSmulSeparatingInertia
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsActionOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulApplyEqOfEqOnInvariants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSecOnNonvanishingOfTameQuotient
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
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory GlobalTheory.DescTheta
open GlobalTheory.LB
variable {X Y : Scheme.{0}}

theorem GlobalTheory.DescTheta.exists_nhds_nonvanishing {G : Over X} {L : LB G.left} (h : PushInvertible G L)
    {W : X.Opens} {O : G.left.Opens} (hO : G.hom ⁻¹ᵁ W ≤ O) (s : Γ(toMod L, O)) (u : G.left)
    (hu : G.hom u ∈ W) (hs : ∃ i, u ∈ G.left.basicOpen (coord s i)) :
    ∃ U : X.Opens, U ≤ W ∧ G.hom u ∈ U ∧ ∀ z ∈ U, ∃ u' : G.left, G.hom u' = z ∧
      ∃ i, u' ∈ G.left.basicOpen (coord s i) := by sorry
