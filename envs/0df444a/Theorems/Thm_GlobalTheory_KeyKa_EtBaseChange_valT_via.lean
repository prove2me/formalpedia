-- Prove2me | Theorems.Thm_GlobalTheory_KeyKa_EtBaseChange_valT_via
-- name    : GlobalTheory.KeyKa.EtBaseChange.valT_via
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:02:49.049877+00:00
-- url     : https://prove2.me/theorems/ee7ca2f4-c2c7-4928-964b-333bc99e863c
-- title:
--   Et Base Change: val T via
-- statement:
--   The Et Base Change construction uses the val T via property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/MemNonzeroLocusVia.lean#L145-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/MemNonzeroLocusVia.lean#L145-L157

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

theorem GlobalTheory.KeyKa.EtBaseChange.valT_via {T : Type} [CommRing T] {l : ℕ} {s' : RR x' l} {s : RR x l} (hs : SecVia x' x φ w s' s)
    (p : Sp T ⟶ x'.P.A.left) (c : x.P.L.ι) (c' : x'.P.L.ι)
    (h : ⊤ ≤ (p ≫ φ) ⁻¹ᵁ x.P.L.U c) (h' : ⊤ ≤ p ⁻¹ᵁ x'.P.L.U c') :
    valT (p ≫ φ) (x.P.L.U c) (s.f c) =
      valT p ((x.P.L.pull φ).U (fun _ => c) ⊓ x'.P.L.U c') (w.s (fun _ => c, c')).val ^ l *
        valT p (x'.P.L.U c') (s'.f c') := by sorry
