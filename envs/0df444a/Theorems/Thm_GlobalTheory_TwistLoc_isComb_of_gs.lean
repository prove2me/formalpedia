-- Prove2me | Theorems.Thm_GlobalTheory_TwistLoc_isComb_of_gs
-- name    : GlobalTheory.TwistLoc.isComb_of_gs
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:08:04.351308+00:00
-- url     : https://prove2.me/theorems/7957b570-e843-40bc-a374-260eb114c2a2
-- title:
--   Twist Loc: is Comb of gs
-- statement:
--   The Twist Loc construction uses the is Comb of gs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsTwistBasisOffPrime.lean#L252-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsTwistBasisOffPrime.lean#L252-L255

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonemptyCubicalPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTwistBasisOffPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TwistLoc
variable {X X' Y Y₁ Y₂ T Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K] {m : ℕ}

theorem GlobalTheory.TwistLoc.isComb_of_gs {π : Y ⟶ T} {N : LB Y} {b : Fin m → LB.Sec N} {s : LB.Sec N} {c : Fin m → Γ(T, ⊤)}
    (h : ∀ y j, y ∈ N.U j →
      gs (𝟙 Y) y (N.U j) (s.f j) = ∑ i, gs (𝟙 Y ≫ π) y ⊤ (c i) * gs (𝟙 Y) y (N.U j) ((b i).f j)) :
    IsComb π b s c := by sorry
