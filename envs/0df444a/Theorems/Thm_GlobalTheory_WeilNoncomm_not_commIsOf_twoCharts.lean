-- Prove2me | Theorems.Thm_GlobalTheory_WeilNoncomm_not_commIsOf_twoCharts
-- name    : GlobalTheory.WeilNoncomm.not_commIsOf_twoCharts
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:08:51.713805+00:00
-- url     : https://prove2.me/theorems/62a14f5c-5969-4843-a647-46e48baa2e79
-- title:
--   Weil Noncomm: not comm Is Of two Charts
-- statement:
--   The Weil Noncomm construction uses the not comm Is Of two Charts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/NotWeilIsGrpPullbackNoncomm.lean#L158-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/NotWeilIsGrpPullbackNoncomm.lean#L158-L175

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_NotWeilIsGrpPullbackNoncomm
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
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.WeilNoncomm
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.H1
variable {S : Scheme.{0}} (G : Over S) [GrpObj G]

theorem GlobalTheory.WeilNoncomm.not_commIsOf_twoCharts {T : Over S} (θx θy : ThetaGrp G (twoCharts G.left) 1 T) (c : Γ(T.left, ⊤)ˣ)
    (z : T.left) (h2 : IsUnit (2 : Γ(T.left, ⊤))) (h₁ : θy.pt * θx.pt ≠ 1) (hx : θy.pt * θx.pt ≠ θx.pt)
    (hy : θy.pt * θx.pt ≠ θy.pt) (hxy : θy.pt * θx.pt ≠ θx.pt * θy.pt) : ¬ CommIsOf G (twoCharts G.left) 1 θx θy c := by sorry
