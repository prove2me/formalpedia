-- Prove2me | Theorems.Thm_GlobalTheory_UU_RelModel_add_formEq
-- name    : GlobalTheory.UU.RelModel.add_formEq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:06:56.933832+00:00
-- url     : https://prove2.me/theorems/f02e3845-7d7d-4639-842a-c1b862cf82f6
-- title:
--   Rel Model: add form Eq
-- statement:
--   The Rel Model construction uses the add form Eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Uniformization/ExistsUniqueSamePtRight.lean#L69-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Uniformization/ExistsUniqueSamePtRight.lean#L69-L97

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

theorem GlobalTheory.UU.RelModel.add_formEq (a b : D.X) (U : Type) [CommGroup U] (h : ((D.P.A ⊗ D.P.A).left ⟶ D.P.A.left) → U) :
    ∏ k, h (addφ D a b k) ^ addε k =
      (∏ k, h ((lift (toUnit _) (fst D.P.A D.P.A)).left ≫ famφT D (𝟙_ _) (a + b) k) ^ DegPre.famε 2 k) *
      (∏ k, h ((lift (toUnit _) (snd D.P.A D.P.A)).left ≫ famφT D (𝟙_ _) (a - b) k) ^ DegPre.famε 2 k) *
      (∏ k, h ((lift (toUnit _) (fst D.P.A D.P.A * snd D.P.A D.P.A)).left ≫ famφT D (𝟙_ _) a k) ^ DegPre.famε 1 k)⁻¹ *
      (∏ k, h ((lift (toUnit _) (fst D.P.A D.P.A * (snd D.P.A D.P.A)⁻¹)).left ≫ famφT D (𝟙_ _) b k) ^ DegPre.famε 1 k)⁻¹ := by sorry
