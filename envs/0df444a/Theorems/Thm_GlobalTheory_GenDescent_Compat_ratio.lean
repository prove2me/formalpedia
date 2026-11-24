-- Prove2me | Theorems.Thm_GlobalTheory_GenDescent_Compat_ratio
-- name    : GlobalTheory.GenDescent.Compat.ratio
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:56:53.060839+00:00
-- url     : https://prove2.me/theorems/50d4f0b2-5f9b-41fc-a08f-2ef2baf5272d
-- title:
--   Compat: ratio
-- statement:
--   The Compat construction uses the ratio property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsGenOfQuotientOfRigid.lean#L101-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsGenOfQuotientOfRigid.lean#L101-L115

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsActionOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsGenOfQuotientOfRigid
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
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory
open GlobalTheory.GenDescent
variable {Y Y' Z : Scheme.{0}}

theorem GlobalTheory.GenDescent.Compat.ratio {N : LB Z} (hN : N.IsLB) {f : Y ⟶ Z} {a b} (ha : Compat N f a)
    (hb : Compat N f b) :
    ∃ c : Γ(Y, ⊤)ˣ, ∀ (W : Scheme.{0}) (k : W ⟶ Y) (w : W) (i : N.ι), f (k w) ∈ N.U i →
      gm k w _ (a i) = gm k w ⊤ c * gm k w _ (b i) := by sorry
