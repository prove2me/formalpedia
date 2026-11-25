-- Prove2me | Theorems.Thm_GlobalTheory_IsoExtend_lbIso_pull_iff_gen
-- name    : GlobalTheory.IsoExtend.lbIso_pull_iff_gen
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:11:06.195891+00:00
-- url     : https://prove2.me/theorems/46f8f9a3-2759-5711-8508-8a719894efeb
-- title:
--   Iso Extend: lb Iso pull iff gen
-- statement:
--   The Iso Extend construction uses the lb Iso pull iff gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/LineBundleIsoExtendOfNormalBase.lean#L70-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/LineBundleIsoExtendOfNormalBase.lean#L70-L72

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueRigidifiedGeneratorExtendNormal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_LineBundleIsoExtendOfNormalBase
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed

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
noncomputable section
open GlobalTheory GlobalTheory.IsoExtend
variable {X Y Y' : Scheme.{0}}

theorem GlobalTheory.IsoExtend.lbIso_pull_iff_gen (L M : LB X) (f : Y ⟶ X) :
    LBIso (L.pull f) (M.pull f) ↔ ∃ t : LB.Gen ((LB.div M L).pull f), t.IsGen := by sorry
