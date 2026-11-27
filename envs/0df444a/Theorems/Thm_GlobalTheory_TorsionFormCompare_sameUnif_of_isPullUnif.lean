-- Prove2me | Theorems.Thm_GlobalTheory_TorsionFormCompare_sameUnif_of_isPullUnif
-- name    : GlobalTheory.TorsionFormCompare.sameUnif_of_isPullUnif
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:43:44.56245+00:00
-- url     : https://prove2.me/theorems/3ea67d87-03c1-4584-886f-6a67ad0ecbc7
-- title:
--   Torsion Form Compare: same Unif of is Pull Unif
-- statement:
--   The Torsion Form Compare construction uses the same Unif of is Pull Unif property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SameUniformizationIdentityPullback.lean#L40-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SameUniformizationIdentityPullback.lean#L40-L75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SameUnifRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_GmMulEqOfResMulEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SameUniformizationIdentityPullback
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
open GlobalTheory GlobalTheory.TorsionFormCompare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem GlobalTheory.TorsionFormCompare.sameUnif_of_isPullUnif : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G G' : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (ε : G' ≅ G) (hD : IsPullDeg (RingHom.id R) D.toPre D.toPre), IsIdPull hD → ∀ (bc : G' ≅ (Over.pullback (specOf (RingHom.id R))).obj G) (U : Unif I D A G) (U' : Unif I D A G'), bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = ε.hom.left → U'.gen.hom = (Over.pullback (jK R)).map ε.hom ≫ U.gen.hom → IsPullUnif (RingHom.id R) hD bc U U' → SameUnif ε U.toUnifPre U'.toUnifPre := by sorry
