-- Prove2me | Theorems.Thm_GlobalTheory_SecLimit_isBas_thick
-- name    : GlobalTheory.SecLimit.isBas_thick
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-27T06:23:13.422408+00:00
-- url     : https://prove2.me/theorems/dd06e280-26b2-592b-87a8-cb2f774f504b
-- title:
--   Sec Limit: is Bas thick
-- statement:
--   The Sec Limit construction uses the is Bas thick property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsUniqueTwistedSectionOfCompatibleLevels.lean#L166-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsUniqueTwistedSectionOfCompatibleLevels.lean#L166-L203

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueLimit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueTwistedSectionOfCompatibleLevels
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
noncomputable section
open GlobalTheory GlobalTheory.SecLimit
variable {V : Type} [CommRing V] [IsDomain V] (D : DegPre V) (k : ℕ) (α : D.X)
variable {D k α}
variable [IsLocalRing V]

theorem GlobalTheory.SecLimit.isBas_thick (hT : SecTwistSt) (hk : 1 ≤ k) {b : Fin (k ^ D.P.g) → Vals D.P.L D.P.A.left}
    (hb : IsBas (cst D.P.L D.P.A.hom) (famVals D k α (𝟙 _)) b) (e : ℕ) :
    IsBas (cst D.P.L (pullback.snd D.P.A.hom (thick V (IsLocalRing.maximalIdeal V) e)))
      (famVals D k α (pullback.fst D.P.A.hom (thick V (IsLocalRing.maximalIdeal V) e)))
      (fun i => pull D.P.L (pullback.fst D.P.A.hom (thick V (IsLocalRing.maximalIdeal V) e)) (b i)) := by sorry
