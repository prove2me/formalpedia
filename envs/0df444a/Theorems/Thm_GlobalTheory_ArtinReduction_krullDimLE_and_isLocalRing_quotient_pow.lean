-- Prove2me | Theorems.Thm_GlobalTheory_ArtinReduction_krullDimLE_and_isLocalRing_quotient_pow
-- name    : GlobalTheory.ArtinReduction.krullDimLE_and_isLocalRing_quotient_pow
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:58:14.832937+00:00
-- url     : https://prove2.me/theorems/2bbe1d57-546f-47c2-9d0b-6216a28698ce
-- title:
--   Artin Reduction: krull Dim LE and is Local Ring quotient pow
-- statement:
--   The Artin Reduction construction uses the krull Dim LE and is Local Ring quotient pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/KrullDimLEAndIsLocalRingQuotientPow.lean#L28-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/KrullDimLEAndIsLocalRingQuotientPow.lean#L28-L46

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_EqZeroOfMemPowMaximal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_KrullDimLEAndIsLocalRingQuotientPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.ArtinReduction

theorem GlobalTheory.ArtinReduction.krullDimLE_and_isLocalRing_quotient_pow {R : Type} [CommRing R] (m : Ideal R)
    [hm : m.IsMaximal] (n : ℕ) :
    Ring.KrullDimLE 0 (R ⧸ m ^ (n + 1)) ∧ IsLocalRing (R ⧸ m ^ (n + 1)) := by sorry
