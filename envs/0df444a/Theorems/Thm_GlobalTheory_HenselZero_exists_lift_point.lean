-- Prove2me | Theorems.Thm_GlobalTheory_HenselZero_exists_lift_point
-- name    : GlobalTheory.HenselZero.exists_lift_point
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:01:01.63465+00:00
-- url     : https://prove2.me/theorems/fe9a9d2e-3946-442a-a8b8-ac94e405f2a9
-- title:
--   Hensel Zero: exists lift point
-- statement:
--   The Hensel Zero construction uses the exists lift point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/TransversalZerosLiftOfIsAdicComplete.lean#L53-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/TransversalZerosLiftOfIsAdicComplete.lean#L53-L120

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsSectionOfTransversal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_TransversalZerosLiftOfIsAdicComplete
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
open GlobalTheory GlobalTheory.HenselZero
open GlobalTheory.KeyKa.EtBaseChange

theorem GlobalTheory.HenselZero.exists_lift_point {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {x : KeyIn O} {xk : KeyIn (IsLocalRing.ResidueField O)} {φ w}
    {n : ℕ} (hg : xk.P.g = x.P.g) {s : Fin x.P.g → RR x n} {sk : Fin xk.P.g → RR xk n}
    (hvia : KeyVia xk x (IsLocalRing.residue O) φ w) (hs : ∀ i, SecVia xk x φ w (sk i) (s (i.cast hg)))
    (zk : Pt xk) (c' : xk.P.L.ι) (h₁ : ⊤ ≤ zk.left ⁻¹ᵁ xk.P.L.U c')
    (h₂ : ∀ i, valT (T := IsLocalRing.ResidueField O) zk.left (xk.P.L.U c') ((sk i).f c') = 0)
    (h₃ : IsUnit (jac xk sk zk c')) :
    ∃ (z : Pt x) (c : x.P.L.ι), spMap (IsLocalRing.residue O) ≫ z.left = zk.left ≫ φ ∧ ⊤ ≤ z.left ⁻¹ᵁ x.P.L.U c ∧
      (∀ i, valT (T := O) z.left (x.P.L.U c) ((s i).f c) = 0) ∧ IsUnit (jac x s z c) ∧
      ∀ (y : x.P.A.left) (pt : Sp (IsLocalRing.ResidueField O)), y ⤳ φ (zk.left pt) →
        (∀ i, y ∉ Out.nonzeroLocus (s i)) → ∃ r : Sp O, z.left r = y := by sorry
