-- Prove2me | Theorems.Thm_GlobalTheory_HomExt_comp_pow_eq_one_of_pullback_hom
-- name    : GlobalTheory.HomExt.comp_pow_eq_one_of_pullback_hom
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:15:18.278555+00:00
-- url     : https://prove2.me/theorems/ae5faf27-6eb4-56c9-822a-73b045ebb59d
-- title:
--   Hom Ext: comp pow eq one of pullback hom
-- statement:
--   The Hom Ext construction uses the comp pow eq one of pullback hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CompPowEqOneOfPullbackHom.lean#L12-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CompPowEqOneOfPullbackHom.lean#L12-L44

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

theorem GlobalTheory.HomExt.comp_pow_eq_one_of_pullback_hom {X T Z : Scheme.{0}} (g : T ⟶ X) {G G' Γ : Over X}
    [GrpObj G] [GrpObj G'] (F : (Over.pullback g).obj G ⟶ (Over.pullback g).obj G') [IsMonHom F]
    (p : Γ ⟶ G) (q : Γ ⟶ G') (c : Z ⟶ Γ.left) (s : Z ⟶ pullback G.hom g)
    (h₁ : s ≫ pullback.fst G.hom g = c ≫ p.left)
    (h₂ : s ≫ F.left ≫ pullback.fst G'.hom g = c ≫ q.left) (n : ℕ)
    (h : c ≫ (p ^ n).left = c ≫ (1 : Γ ⟶ G).left) :
    c ≫ (q ^ n).left = c ≫ (1 : Γ ⟶ G').left := by sorry
