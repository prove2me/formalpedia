-- Prove2me | Theorems.Thm_GlobalTheory_PowBasis_comb_iff
-- name    : GlobalTheory.PowBasis.comb_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:51:21.25177+00:00
-- url     : https://prove2.me/theorems/916ba551-7c97-4eee-a5bd-3dc195717c32
-- title:
--   Pow Basis: comb iff
-- statement:
--   The Pow Basis construction uses the comb iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsBasisOfFormEq.lean#L22-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsBasisOfFormEq.lean#L22-L44

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsBasisOfFormEq
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowBasis

theorem GlobalTheory.PowBasis.comb_iff {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {m : ℕ} (s : LB.Sec (LB.LinComb L φ ε)) (b : Fin m → LB.Sec (LB.LinComb L φ ε)) (r : Fin m → Γ(Y, ⊤)) :
    (∀ j, s.f j = ∑ i, (Y.presheaf.map (homOfLE le_top).op).hom (r i) * (b i).f j) ↔
      ∀ y J, Good L y J → sval s (𝟙 Y) y J = ∑ i, gs (𝟙 Y) y ⊤ (r i) * sval (b i) (𝟙 Y) y J := by sorry
