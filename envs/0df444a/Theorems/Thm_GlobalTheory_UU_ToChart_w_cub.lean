-- Prove2me | Theorems.Thm_GlobalTheory_UU_ToChart_w_cub
-- name    : GlobalTheory.UU.ToChart.w_cub
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T15:56:53.102808+00:00
-- url     : https://prove2.me/theorems/2f6c6aeb-87f6-5efd-aacc-c2c8397dc9b4
-- title:
--   To Chart: w cub
-- statement:
--   The To Chart construction uses the w cub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/GmResPull.lean#L137-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/GmResPull.lean#L137-L183

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SameB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_GmResPull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.ToChart
variable {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (e : ℕ)
variable {I e} {D : DegPre R} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
variable {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} (U : PreU I D A G)

theorem GlobalTheory.UU.ToChart.w_cub (e : ℕ) (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
    (x : Fin 3 → (T ⟶ thickObj R I e G)) (jL : thK → U.P.L.L.ι) (jM : thK → D.P.L.ι)
    (cL : LB.Coh U.P.L.L (fun k => (lift ((Over.map (thick R I e)).map (x 0) ≫ fstG I e G)
      (lift ((Over.map (thick R I e)).map (x 1) ≫ fstG I e G)
        ((Over.map (thick R I e)).map (x 2) ≫ fstG I e G))).left ≫ thφ G (x3 G) k) jL)
    (cM : LB.Coh D.P.L (fun k => (lift ((Over.map (thick R I e)).map (x 0) ≫ (U.gt e).pG)
      (lift ((Over.map (thick R I e)).map (x 1) ≫ (U.gt e).pG)
        ((Over.map (thick R I e)).map (x 2) ≫ (U.gt e).pG))).left ≫
          thφ D.P.A (x3 D.P.A) k) jM)
    (V : T.left.Opens)
      (hB : V ≤ (lift ((Over.map (thick R I e)).map (x 0) ≫ (U.gt e).pG)
        (lift ((Over.map (thick R I e)).map (x 1) ≫ (U.gt e).pG)
          ((Over.map (thick R I e)).map (x 2) ≫ (U.gt e).pG))).left ⁻¹ᵁ
            (Theta D.P.A D.P.L).U jM)
      (hG : V ≤ (lift ((Over.map (thick R I e)).map (x 0) ≫ fstG I e G)
        (lift ((Over.map (thick R I e)).map (x 1) ≫ fstG I e G)
          ((Over.map (thick R I e)).map (x 2) ≫ fstG I e G))).left ⁻¹ᵁ (Theta G U.P.L.L).U jL)
      (hw : ∀ k : thK, V ≤ (psum (thickObj R I e G) x k.down).left ⁻¹ᵁ
        ((D.P.L.pull (U.gt e).pG.left).U (fun _ => jM k) ⊓
          (U.P.L.L.pull (fstG I e G).left).U (fun _ => jL k))) :
      res hB (pullU _ _ (D.cub.t.s jM)) =
        (∏ k : thK, res (hw k) (pullU (psum (thickObj R I e G) x k.down).left _
          ((U.w e).s (fun _ => jM k, fun _ => jL k))) ^ thε k) *
        res hG (pullU _ _ (U.P.c.t.s jL)) := by sorry
