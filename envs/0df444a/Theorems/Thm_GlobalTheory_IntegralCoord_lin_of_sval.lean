-- Prove2me | Theorems.Thm_GlobalTheory_IntegralCoord_lin_of_sval
-- name    : GlobalTheory.IntegralCoord.lin_of_sval
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:20:44.285017+00:00
-- url     : https://prove2.me/theorems/dcd5c0df-b29f-4fce-a868-8773c398d7f2
-- title:
--   Integral Coord: lin of sval
-- statement:
--   The Integral Coord construction uses the lin of sval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ExistsBasisOfEq.lean#L20-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ExistsBasisOfEq.lean#L20-L39

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

theorem GlobalTheory.IntegralCoord.lin_of_sval {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {s : LB.Sec (LB.LinComb L φ ε)}
    {n : ℕ} (b : Fin n → Γ(Y, ⊤)) (t : Fin n → LB.Sec (LB.LinComb L φ ε))
    (H : ∀ (y : Y) (J : (Y ⟶ X) → L.ι), Good L y J →
      sval s (𝟙 Y) y J = ∑ i, gs (𝟙 Y) y ⊤ (b i) * sval (t i) (𝟙 Y) y J) (j : K → L.ι) :
    s.f j = ∑ i, resTop (LB.wchart L φ j) (b i) * (show Γ(Y, LB.wchart L φ j) from (t i).f j) := by sorry
