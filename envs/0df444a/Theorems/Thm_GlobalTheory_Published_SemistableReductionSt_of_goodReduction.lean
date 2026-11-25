-- Prove2me | Theorems.Thm_GlobalTheory_Published_SemistableReductionSt_of_goodReduction
-- name    : GlobalTheory.Published.SemistableReductionSt.of_goodReduction
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:24:13.601305+00:00
-- url     : https://prove2.me/theorems/83c055c9-b5c9-5629-b95e-eba32773f950
-- title:
--   Semistable Reduction St: of good Reduction
-- statement:
--   The Semistable Reduction St construction uses the of good Reduction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/SemistableReduction₂/SemistableReductionSt.lean#L44-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/SemistableReduction₂/SemistableReductionSt.lean#L44-L53

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_IsAbelianSchemeAndExtendOfGenericHoms
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_SemistableReduction__SemistableReductionSt_184d2c70c106979e
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
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.SemistableReductionSt
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]

theorem GlobalTheory.Published.SemistableReductionSt.of_goodReduction (G : Over (Sp (integralClosure ℤ_[p] K))) [GrpObj G] (hG : IsAbelianScheme G) :
    IsAbelianScheme ((Over.pullback (spMap (algebraMap (integralClosure ℤ_[p] K) K))).obj G) ∧
    ∃ (K' : IntermediateField ℚ_[p] (PadicAlgCl p)) (h : K ≤ K'), FiniteDimensional ℚ_[p] K' ∧
      ∃ (G' : Over (Sp (integralClosure ℤ_[p] K'))) (_ : GrpObj G'), IsSemiAbelian G' ∧
        ∃ φ : pullback G'.hom (spMap (algebraMap (integralClosure ℤ_[p] K') K')) ⟶
            ((Over.pullback (spMap (algebraMap (integralClosure ℤ_[p] K) K))).obj G).left,
          IsGrpPullback ((Over.pullback (spMap (algebraMap (integralClosure ℤ_[p] K') K'))).obj G')
            ((Over.pullback (spMap (algebraMap (integralClosure ℤ_[p] K) K))).obj G)
            (spMap (IntermediateField.inclusion h).toRingHom) φ := by sorry
