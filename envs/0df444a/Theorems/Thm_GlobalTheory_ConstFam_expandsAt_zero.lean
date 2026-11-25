-- Prove2me | Theorems.Thm_GlobalTheory_ConstFam_expandsAt_zero
-- name    : GlobalTheory.ConstFam.expandsAt_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T15:28:17.083448+00:00
-- url     : https://prove2.me/theorems/ba27b02f-6cb3-4ca5-8924-0dfa72d9df71
-- title:
--   Const Fam: expands At zero
-- statement:
--   The Const Fam construction uses the expands At zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsSmulMemSpanOfExpandsAt.lean#L44-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsSmulMemSpanOfExpandsAt.lean#L44-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpandsAtSecIsMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpandsAtSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsFETranslateFeTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSmulMemSpanOfExpandsAt
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ConstFam
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.FieldBaseChange
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] (U : UnifPre I D A G) {j n : ℕ}

theorem GlobalTheory.ConstFam.expandsAt_zero
    {σ : SecOver G.hom (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (j : ℤ)))}
    {f : ∀ χ, SecBMod D.toPre j χ} (h : U.ExpandsAt n j σ f) :
    U.ExpandsAt n j (0 : SecOver G.hom _) (0 : ∀ χ, SecBMod D.toPre j χ) := by sorry
