-- Prove2me | Theorems.Thm_GlobalTheory_UU_prod_famT
-- name    : GlobalTheory.UU.prod_famT
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:24:12.061243+00:00
-- url     : https://prove2.me/theorems/e879551f-7ab6-4b9b-a022-6a1af2ea9508
-- title:
--   UU: prod fam T
-- statement:
--   The UU construction uses the prod fam T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsIsProdB.lean#L19-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsIsProdB.lean#L19-L30

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SvalTwistOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsIsProdB
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
open GlobalTheory GlobalTheory.UU

theorem GlobalTheory.UU.prod_famT {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R)))
    (α : D.X) (k : ℕ) {U : Type} [CommGroup U] (h : ((T ⊗ D.P.A).left ⟶ D.P.A.left) → U) :
    ∏ i, h (famφT D T α i) ^ DegPre.famε k i =
      h (snd T D.P.A).left ^ ((k : ℤ) - 1) * h (DVR.cP D (T ⊗ D.P.A) α * snd T D.P.A).left *
        (h (DVR.cP D (T ⊗ D.P.A) α).left)⁻¹ * h (1 : T ⊗ D.P.A ⟶ D.P.A).left := by sorry
