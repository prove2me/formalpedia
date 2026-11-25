-- Prove2me | Theorems.Thm_GlobalTheory_ExpCmp_prod_fam
-- name    : GlobalTheory.ExpCmp.prod_fam
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:23:17.62483+00:00
-- url     : https://prove2.me/theorems/cf6eb0d5-c2e4-47da-a201-759fea8618c1
-- title:
--   Exp Cmp: prod fam
-- statement:
--   The Exp Cmp construction uses the prod fam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/UnitMapSnd.lean#L62-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/UnitMapSnd.lean#L62-L78

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_ExistsUniquePartner
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_MatchingSectionsExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnitMapSnd
import Theorems.Thm_GlobalTheory_ExpTrans_prod_fam
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_prod_fam

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
noncomputable section
open GlobalTheory GlobalTheory.ExpCmp
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ExpTrans GlobalTheory.UnitSec
variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V]

theorem GlobalTheory.ExpCmp.prod_fam {D : DegPre R} {T : Over (Spec (CommRingCat.of R))} (p : T ⟶ D.P.A) (k : ℕ)
    {M : Type} [CommGroup M] (ω : (T.left ⟶ D.P.A.left) → M) (α : D.X) :
    (∏ a, ω (p.left ≫ D.famφB α a) ^ DegPre.famε k a) * ∏ a, ω (D.Oφ p α a) ^ Oinvε a =
      ω p.left ^ k := by sorry
