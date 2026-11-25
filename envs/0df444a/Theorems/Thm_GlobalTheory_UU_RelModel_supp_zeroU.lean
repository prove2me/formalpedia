-- Prove2me | Theorems.Thm_GlobalTheory_UU_RelModel_supp_zeroU
-- name    : GlobalTheory.UU.RelModel.supp_zeroU
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T16:11:43.535068+00:00
-- url     : https://prove2.me/theorems/6ec82852-d930-5a56-a5a0-f872647f0155
-- title:
--   Rel Model: supp zero U
-- statement:
--   The Rel Model construction uses the supp zero U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Uniformization/ExistsUniqueSamePtRight.lean#L214-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Uniformization/ExistsUniqueSamePtRight.lean#L214-L221

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqOfSecConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePtRight
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.RelModel
open GlobalTheory.UnifZero ReciprocityTheory.ChartRestriction.G.Out.Inh
variable {X Y Z : Scheme.{0}} {K : Type} [Fintype K]
variable (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ)

theorem GlobalTheory.UU.RelModel.supp_zeroU : (zeroU R I).Supp F k PUnit.unit := by sorry
