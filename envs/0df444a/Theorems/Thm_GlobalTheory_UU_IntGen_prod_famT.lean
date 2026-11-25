-- Prove2me | Theorems.Thm_GlobalTheory_UU_IntGen_prod_famT
-- name    : GlobalTheory.UU.IntGen.prod_famT
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T16:29:58.36396+00:00
-- url     : https://prove2.me/theorems/516ddcd3-a6c3-4bd9-a348-ff8f0898cbd5
-- title:
--   Int Gen: prod fam T
-- statement:
--   The Int Gen construction uses the prod fam T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsGenT.lean#L41-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsGenT.lean#L41-L52

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SvalTwistOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGenT
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
open GlobalTheory.UU
open ReciprocityTheory.ChartRestriction.G.DVR
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.IntGen
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem GlobalTheory.UU.IntGen.prod_famT {T T' : Over (Spec (CommRingCat.of R))} (ρ : T' ⟶ T ⊗ D.P.A) (α : D.X) (k : ℕ) {U : Type}
    [CommGroup U] (h : (T'.left ⟶ D.P.A.left) → U) : ∏ i, h (ρ.left ≫ famφT D T α i) ^ DegPre.famε k i =
      h (ρ ≫ snd _ _).left ^ ((k : ℤ) - 1) * h (cP D T' α * (ρ ≫ snd _ _)).left * (h (cP D T' α).left)⁻¹ *
        h (1 : T' ⟶ D.P.A).left := by sorry
