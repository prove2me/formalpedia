-- Prove2me | Theorems.Thm_GlobalTheory_ZJ_SplitPull_exists_basis_pushout
-- name    : GlobalTheory.ZJ.SplitPull.exists_basis_pushout
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:49:40.357524+00:00
-- url     : https://prove2.me/theorems/e6c3b792-5b29-44f4-9a51-04cb1fad32d8
-- title:
--   Split Pull: exists basis pushout
-- statement:
--   The Split Pull construction uses the exists basis pushout property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/PullPullAndSplitPull.lean#L20-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/PullPullAndSplitPull.lean#L20-L44

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

theorem GlobalTheory.ZJ.SplitPull.exists_basis_pushout {R R' : CommRingCat.{0}} (hR : IsField R) (b : R ⟶ R') :
    ∃ (J : Type) (e : J → R'), ∀ (A A' : CommRingCat.{0}) (a : R ⟶ A) (p : A ⟶ A') (q : R' ⟶ A'),
      IsPushout a b p q →
      (∀ u : A', ∃ (s : Finset J) (x : J → A), u = ∑ l ∈ s, p.hom (x l) * q.hom (e l)) ∧
      ∀ (s : Finset J) (x : J → A), ∑ l ∈ s, p.hom (x l) * q.hom (e l) = 0 → ∀ l ∈ s, x l = 0 := by sorry
