-- Prove2me | Theorems.Thm_GlobalTheory_HomExt_exists_iso_pullback_pullback
-- name    : GlobalTheory.HomExt.exists_iso_pullback_pullback
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:09:49.91881+00:00
-- url     : https://prove2.me/theorems/c5e6c44f-a4a0-442b-97ab-08cdb0a649a3
-- title:
--   Hom Ext: exists iso pullback pullback
-- statement:
--   The Hom Ext construction uses the exists iso pullback pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CompPowEqOneOfPullbackHom.lean#L46-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CompPowEqOneOfPullbackHom.lean#L46-L61

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueOfIsAdicComplete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SemiAbelianTorsionFiniteAndClosedPointFiniteOrde
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CompPowEqOneOfPullbackHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.HomExt

theorem GlobalTheory.HomExt.exists_iso_pullback_pullback {X T Z : Scheme.{0}} (p : Z ⟶ T) (f : T ⟶ X) (r : Z ⟶ X)
    (h : p ≫ f = r) (G : Over X) [GrpObj G] :
    ∃ e : (Over.pullback r).obj G ≅ (Over.pullback p).obj ((Over.pullback f).obj G),
      IsMonHom e.hom ∧ e.hom.left ≫ pullback.fst (pullback.snd G.hom f) p ≫ pullback.fst G.hom f =
        pullback.fst G.hom r := by sorry
