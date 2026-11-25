-- Prove2me | Theorems.Thm_GlobalTheory_ZM_FullLevel_dim_generic_chart
-- name    : GlobalTheory.ZM.FullLevel.dim_generic_chart
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:43:36.970112+00:00
-- url     : https://prove2.me/theorems/56fddf65-8294-42b6-84ff-1d11584e7b62
-- title:
--   Full Level: dim generic chart
-- statement:
--   The Full Level construction uses the dim generic chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MinimalAndDimLe.lean#L48-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MinimalAndDimLe.lean#L48-L134

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MinimalAndDimLe
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
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.FullLevel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj TensorProduct

theorem GlobalTheory.ZM.FullLevel.dim_generic_chart {o K : Type} [CommRing o] [IsDomain o] [Field K]
    [Algebra o K] [IsFractionRing o K]
    {U : Scheme.{0}} (s : U ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp o) (d : WithBot ℕ∞)
    (h : ∀ (R : Type) [CommRing R] [Algebra o R] (x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ U), IsOpenImmersion x →
      x ≫ s = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap o R) →
      ∀ q ∈ minimalPrimes (FractionRing o ⊗[o] R), d ≤ ringKrullDim ((FractionRing o ⊗[o] R) ⧸ q))
    (R : Type) [CommRing R] (x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ pullback s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap o K)))
    [IsOpenImmersion x]
    (q : Ideal R) (hq : q ∈ minimalPrimes R) : d ≤ ringKrullDim (R ⧸ q) := by sorry
