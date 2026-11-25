-- Prove2me | Theorems.Thm_GlobalTheory_UU_ToChart_w_even
-- name    : GlobalTheory.UU.ToChart.w_even
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T16:00:01.108541+00:00
-- url     : https://prove2.me/theorems/adf5666e-14ce-5f18-9eb1-48a5aa355b3b
-- title:
--   To Chart: w even
-- statement:
--   The To Chart construction uses the w even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/GmResPull.lean#L99-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/GmResPull.lean#L99-L135

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

theorem GlobalTheory.UU.ToChart.w_even (e : ℕ) (jS : Fin 2 → U.P.L.L.ι) (jT : Fin 2 → D.P.L.ι)
    (cS : LB.Coh U.P.L.L (fun k => (fstG I e G).left ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → _) k) jS)
    (cT : LB.Coh D.P.L
      (fun k => (U.gt e).pG.left ≫ (![(ι[D.P.A]).left, 𝟙 D.P.A.left] : Fin 2 → _) k) jT)
    (V : (thickObj R I e G).left.Opens)
      (h₁ : V ≤ (U.gt e).pG.left ⁻¹ᵁ (LB.LinComb D.P.L (K := Fin 2)
        ![(ι[D.P.A]).left, 𝟙 D.P.A.left] ![1, -1]).U jT)
      (h₂ : V ≤ (D.P.L.pull (U.gt e).pG.left).U (fun _ => jT 1) ⊓
        (U.P.L.L.pull (fstG I e G).left).U (fun _ => jS 1))
      (h₃ : V ≤ (ι[thickObj R I e G]).left ⁻¹ᵁ ((D.P.L.pull (U.gt e).pG.left).U (fun _ => jT 0) ⊓
        (U.P.L.L.pull (fstG I e G).left).U (fun _ => jS 0)))
      (h₄ : V ≤ (fstG I e G).left ⁻¹ᵁ (LB.LinComb U.P.L.L (K := Fin 2)
        ![(ι[G]).left, 𝟙 G.left] ![1, -1]).U jS) :
      res h₁ (pullU (U.gt e).pG.left _ (D.sym.s jT)) *
        res h₂ ((U.w e).s (fun _ => jT 1, fun _ => jS 1)) =
      res h₃ (pullU (ι[thickObj R I e G]).left _ ((U.w e).s (fun _ => jT 0, fun _ => jS 0))) *
        res h₄ (pullU (fstG I e G).left _ (U.P.sym.s jS)) := by sorry
