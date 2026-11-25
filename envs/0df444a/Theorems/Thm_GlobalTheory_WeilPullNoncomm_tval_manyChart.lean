-- Prove2me | Theorems.Thm_GlobalTheory_WeilPullNoncomm_tval_manyChart
-- name    : GlobalTheory.WeilPullNoncomm.tval_manyChart
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:08:17.426449+00:00
-- url     : https://prove2.me/theorems/f0439ed4-672e-49b4-83fe-1beb9035df6c
-- title:
--   Weil Pull Noncomm: tval many Chart
-- statement:
--   The Weil Pull Noncomm construction uses the tval many Chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NotWeilIsGrpPullback.lean#L91-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NotWeilIsGrpPullback.lean#L91-L102

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NotWeilIsGrpPullback
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.WeilPullNoncomm
open GlobalTheory.CommPairing
variable {S : Scheme.{0}} {G : Over S} [GrpObj G]

theorem GlobalTheory.WeilPullNoncomm.tval_manyChart {κ : Type} (v : κ → Γ(G.left, ⊤)ˣ) {k : ℤ} {T : Over S} (θ : ThetaGrp G (manyChart v) k T)
    {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ G).left) (z : Z) (J J' : (Z ⟶ G.left) → κ) :
    tval θ r z J = ((gm (r ≫ (snd T G).left) z ⊤ (v (J (r ≫ (snd T G).left))) *
        (gm (r ≫ (snd T G).left) z ⊤ (v (J' (r ≫ (snd T G).left))))⁻¹) ^ k *
      (gm (r ≫ (translPt G θ.pt).left) z ⊤ (v (J (r ≫ (translPt G θ.pt).left))) *
        (gm (r ≫ (translPt G θ.pt).left) z ⊤ (v (J' (r ≫ (translPt G θ.pt).left))))⁻¹) ^ (-k)) * tval θ r z J' := by sorry
