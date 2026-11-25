-- Prove2me | Theorems.Thm_GlobalTheory_ZJ_SplitPull_exists_basis_sections
-- name    : GlobalTheory.ZJ.SplitPull.exists_basis_sections
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T16:59:37.694614+00:00
-- url     : https://prove2.me/theorems/bcb3e215-44c6-5bcf-bf3a-5f4f6cc1f4aa
-- title:
--   Split Pull: exists basis sections
-- statement:
--   The Split Pull construction uses the exists basis sections property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/PullPullAndSplitPull.lean#L46-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/PullPullAndSplitPull.lean#L46-L75

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

theorem GlobalTheory.ZJ.SplitPull.exists_basis_sections {K K' : Type} [Field K] [Field K'] (f : Sp K' ⟶ Sp K) :
    ∃ (J : Type) (e : J → Γ(Sp K', ⊤)), ∀ (X Y : Scheme.{0}) (g : Y ⟶ X) (iX : X ⟶ Sp K) (iY : Y ⟶ Sp K'),
      IsPullback g iY iX f →
      (∀ U : X.Opens, IsAffineOpen U → ∀ u : Γ(Y, g ⁻¹ᵁ U), ∃ (s : Finset J) (x : J → Γ(X, U)),
        u = ∑ l ∈ s, (g.app U).hom (x l) * (iY.appLE ⊤ (g ⁻¹ᵁ U) le_top).hom (e l)) ∧
      ∀ (s : Finset J) (x : J → Γ(X, ⊤)), ∑ l ∈ s, g.appTop.hom (x l) * iY.appTop.hom (e l) = 0 →
        ∀ l ∈ s, x l = 0 := by sorry
