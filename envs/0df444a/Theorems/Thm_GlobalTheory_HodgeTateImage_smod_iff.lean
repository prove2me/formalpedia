-- Prove2me | Theorems.Thm_GlobalTheory_HodgeTateImage_smod_iff
-- name    : GlobalTheory.HodgeTateImage.smod_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:47:49.791215+00:00
-- url     : https://prove2.me/theorems/755ffb3e-7092-4c72-bf21-80e560c3a946
-- title:
--   Hodge Tate Image: smod iff
-- statement:
--   The Hodge Tate Image construction uses the smod iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsUniqueIsAl.lean#L135-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsUniqueIsAl.lean#L135-L140

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ThmASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitOfBijectiveMulNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowEqScaleAndExistsUniqueTorsion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsUniqueIsAl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HodgeTateImage
open GlobalTheory.TangentPow GlobalTheory.GmPoints
variable {O : Type} [CommRing O] {G : Over (Spec (CommRingCat.of O))} [GrpObj G] {p : ℕ}
variable (χ : Tv G p)

theorem GlobalTheory.HodgeTateImage.smod_iff (n : ℕ) (a b : O) :
    a ≡ b [SMOD (Ideal.span {(p : O)} ^ n • ⊤ : Submodule O O)] ↔
      algebraMap O (O ⧸ Ideal.span {(p : O) ^ n}) a =
        algebraMap O (O ⧸ Ideal.span {(p : O) ^ n}) b := by sorry
