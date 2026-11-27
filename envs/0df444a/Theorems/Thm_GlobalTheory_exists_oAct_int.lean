-- Prove2me | Theorems.Thm_GlobalTheory_exists_oAct_int
-- name    : GlobalTheory.exists_oAct_int
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:59:33.600982+00:00
-- url     : https://prove2.me/theorems/a4402000-0397-4bab-af09-600933b79279
-- title:
--   Global Theory: exists o Act int
-- statement:
--   The Global Theory construction uses the exists o Act int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/RosatiAdjOfPoints.lean#L125-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/RosatiAdjOfPoints.lean#L125-L130

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RosatiAdjMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RosatiAdjOfPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory

theorem GlobalTheory.exists_oAct_int : Out.CubeSt → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S),
    ∃ ρ : P.OAct ℤ, ∀ a : ℤ, ρ.act a = (𝟙 P.A : P.A ⟶ P.A) ^ a := by sorry
