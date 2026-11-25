-- Prove2me | Theorems.Thm_GlobalTheory_ZJ_SplitPull_hasWt_coeff
-- name    : GlobalTheory.ZJ.SplitPull.hasWt_coeff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T17:03:43.832977+00:00
-- url     : https://prove2.me/theorems/9c01171e-b084-5512-9aa1-2d672e1cfd45
-- title:
--   Split Pull: has Wt coeff
-- statement:
--   The Split Pull construction uses the has Wt coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/PullPullAndSplitPull.lean#L130-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/PullPullAndSplitPull.lean#L130-L174

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsAffineSplitTorusLeft
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_PullPullAndSplitPull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
noncomputable section
open GlobalTheory GlobalTheory.ZJ GlobalTheory.ZJ.SplitPull
open GlobalTheory.UU
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {X : Type} [AddCommGroup X] {G : Over S} {G' : Over S'} [GrpObj G]
  [GrpObj G'] {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G f F) {i : splitTorus S X ⟶ G}
  {i' : splitTorus S' X ⟶ G'} (hi : TorusCompat f F i' i)
include hF hi

theorem GlobalTheory.ZJ.SplitPull.hasWt_coeff {J : Type} (e : J → Γ(S', ⊤))
    (he : ∀ (Y : Over S) (s : Finset J) (x : J → Γ(Y.left, ⊤)),
      ∑ l ∈ s, (pullback.fst Y.hom f).appTop.hom (x l) * (pullback.snd Y.hom f).appTop.hom (e l) = 0 →
        ∀ l ∈ s, x l = 0)
    {V : G.left.Opens} (s : Finset J) (x : J → Γ(G.left, V))
    (hu : HasWt i' (F ⁻¹ᵁ V) (∑ l ∈ s, (F.app V).hom (x l) * (G'.hom.appLE ⊤ (F ⁻¹ᵁ V) le_top).hom (e l)) 0) :
    ∀ l ∈ s, HasWt i V (x l) 0 := by sorry
