-- Prove2me | Theorems.Thm_GlobalTheory_secIsMul_gs
-- name    : GlobalTheory.secIsMul_gs
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:09:53.670393+00:00
-- url     : https://prove2.me/theorems/09d51d5f-f262-4424-99a4-daec9b48844b
-- title:
--   Global Theory: sec Is Mul gs
-- statement:
--   The Global Theory construction uses the sec Is Mul gs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ExpandsAtSecIsMul.lean#L15-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ExpandsAtSecIsMul.lean#L15-L20

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpandsAtSecIsMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem GlobalTheory.secIsMul_gs {R : Type} [CommRing R] {Y Z : Scheme.{0}} {p : Y ⟶ Spec (CommRingCat.of R)} {L : LB Y} {a : R}
    {σ τ : LB.Sec L} (h : SecIsMul p a σ τ) (q : Z ⟶ Y) (z : Z) (j : L.ι) (hz : q z ∈ L.U j) :
    gs q z (L.U j) (σ.f j) = cst (q ≫ p) z a * gs q z (L.U j) (τ.f j) := by sorry
