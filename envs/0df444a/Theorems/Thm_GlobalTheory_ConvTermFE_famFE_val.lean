-- Prove2me | Theorems.Thm_GlobalTheory_ConvTermFE_famFE_val
-- name    : GlobalTheory.ConvTermFE.famFE_val
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:15:25.316931+00:00
-- url     : https://prove2.me/theorems/6e4429df-b0cb-49b6-89d2-a49a0e9a8ee8
-- title:
--   Conv Term FE: fam FE val
-- statement:
--   The Conv Term FE construction uses the fam FE val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ConvTermFe.lean#L18-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ConvTermFe.lean#L18-L25

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TranslationUnitMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ConvTermFe
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
open GlobalTheory GlobalTheory.ConvTermFE
open ReciprocityTheory.ChartRestriction.G.DVR

theorem GlobalTheory.ConvTermFE.famFE_val (hG : GlobalFnsSt) {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] (k : ℕ) (s : Raw D F k) (hs : DegPre.FamFE D F k s) (mu β : D.X)
    (Z : Over (Spec (CommRingCat.of R))) (r : Z ⟶ DegPre.BF D F) (z : Z.left) (J) (hJ : Good D.P.L z J) :
    sval (s (β + k • mu)) r.left z J = sval (s β) (r ≫ DegPre.trF D F mu).left z J *
      (uVal D F k β (cP D _ mu) r z J * val (DegPre.famMult D F k mu β) (r ≫ fst _ _).left z J).val := by sorry
