-- Prove2me | Theorems.Thm_GlobalTheory_WCub_clause_iff
-- name    : GlobalTheory.WCub.clause_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:27:31.849407+00:00
-- url     : https://prove2.me/theorems/d2170e96-fcca-41f8-b865-e963e012ef3a
-- title:
--   WCub: clause iff
-- statement:
--   The WCub construction uses the clause iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TripleProductPointCompProjection.lean#L20-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TripleProductPointCompProjection.lean#L20-L45

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TripleProductPointCompProjection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.WCub
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.WCub.clause_iff {T XB XG E : Scheme.{0}} {K : Type} [Fintype K] (mB : T ⟶ XB) (mG : T ⟶ XG) (p : K → (T ⟶ E))
    (UB : XB.Opens) (UG : XG.Opens) (W : K → E.Opens) (a : Γ(XB, UB)ˣ) (b : Γ(XG, UG)ˣ) (c : ∀ k, Γ(E, W k)ˣ)
    (ε : K → ℤ) :
    (∀ (V : T.Opens) (hB : V ≤ mB ⁻¹ᵁ UB) (hG : V ≤ mG ⁻¹ᵁ UG) (hw : ∀ k, V ≤ p k ⁻¹ᵁ W k),
      res hB (pullU mB UB a) = (∏ k, res (hw k) (pullU (p k) (W k) (c k)) ^ ε k) * res hG (pullU mG UG b)) ↔
    ∀ y : T, mB y ∈ UB → mG y ∈ UG → (∀ k, p k y ∈ W k) →
      gm mB y UB a = (∏ k, gm (p k) y (W k) (c k) ^ ε k) * gm mG y UG b := by sorry
