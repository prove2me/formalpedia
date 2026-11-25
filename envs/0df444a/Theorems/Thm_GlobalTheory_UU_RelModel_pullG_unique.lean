-- Prove2me | Theorems.Thm_GlobalTheory_UU_RelModel_pullG_unique
-- name    : GlobalTheory.UU.RelModel.pullG_unique
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T16:07:08.229835+00:00
-- url     : https://prove2.me/theorems/814b39f4-d3fb-4223-bb69-cc0a2ec38fb8
-- title:
--   Rel Model: pull G unique
-- statement:
--   The Rel Model construction uses the pull G unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Uniformization/ExistsUniqueSamePtRight.lean#L137-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Uniformization/ExistsUniqueSamePtRight.lean#L137-L156

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqOfSecConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePtRight
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
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem GlobalTheory.UU.RelModel.pullG_unique (U : PreU I D A G) {T : Over (Spec (CommRingCat.of R))} (φ : TF (R := R) F ⟶ T) (k : ℕ)
    (σ : U.SecGT T k) {t t'} (h : U.PullG F φ k σ t) (h' : U.PullG F φ k σ t') (j) : t.f j = t'.f j := by sorry
