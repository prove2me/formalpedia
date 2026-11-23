-- Prove2me | Theorems.Thm_GlobalTheory_IntegralCoord_exists_basis_of_eq
-- name    : GlobalTheory.IntegralCoord.exists_basis_of_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:10:16.294186+00:00
-- url     : https://prove2.me/theorems/b25b07d4-ed14-4981-b80d-de81709d9f87
-- title:
--   Integral Coord: exists basis of eq
-- statement:
--   The Integral Coord construction uses the exists basis of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ExistsBasisOfEq.lean#L41-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ExistsBasisOfEq.lean#L41-L49

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExistsBasisOfEq
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IntegralCoord
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation

theorem GlobalTheory.IntegralCoord.exists_basis_of_eq {S : Scheme.{0}} {A T : Over S} {L : LB A.left} {K : Type} [Fintype K]
    {φ : K → (A.left ⟶ A.left)} {ε : K → ℤ} {m : ℕ} (b₀ : Fin m → LB.Sec (LB.LinComb L φ ε))
    (hb : IsSecBasis (T := T) (A := A) _ (fun i => DVR.pullSec L φ ε (b₀ i) (snd T A).left))
    (φ' : K → ((T ⊗ A).left ⟶ A.left)) (h : φ' = fun k => (snd T A).left ≫ φ k) :
    ∃ b : Fin m → LB.Sec (LB.LinComb L φ' ε), IsSecBasis (T := T) (A := A) _ b ∧
      ∀ i (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J : (Z ⟶ A.left) → L.ι), Good L z J →
        sval (b i) r z J = sval (b₀ i) (r ≫ (snd T A).left) z J := by sorry
