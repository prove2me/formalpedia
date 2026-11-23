-- Prove2me | Theorems.Thm_GlobalTheory_KeyKa_EtBaseChange_mem_nonzeroLocus_via
-- name    : GlobalTheory.KeyKa.EtBaseChange.mem_nonzeroLocus_via
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:03:51.428215+00:00
-- url     : https://prove2.me/theorems/4007ba9c-656b-472a-ab8b-92c88ebed7ea
-- title:
--   Et Base Change: mem nonzero Locus via
-- statement:
--   The Et Base Change construction uses the mem nonzero Locus via property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/MemNonzeroLocusVia.lean#L159-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/MemNonzeroLocusVia.lean#L159-L170

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MemNonzeroLocusVia
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.KeyKa GlobalTheory.KeyKa.EtBaseChange
variable {R R' : Type} [CommRing R] [CommRing R'] {x : KeyIn R} {x' : KeyIn R'} {φ : x'.P.A.left ⟶ x.P.A.left}
  {w : LB.Iso x'.P.L (x.P.L.pull φ)}

theorem GlobalTheory.KeyKa.EtBaseChange.mem_nonzeroLocus_via {l : ℕ} {s' : RR x' l} {s : RR x l} (hs : SecVia x' x φ w s' s) (y : x'.P.A.left)
    (hy : φ y ∈ Out.nonzeroLocus s) : y ∈ Out.nonzeroLocus s' := by sorry
