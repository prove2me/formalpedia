-- Prove2me | Theorems.Thm_GlobalTheory_ToricData_weilQkIs_pt
-- name    : GlobalTheory.ToricData.weilQkIs_pt
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:37:19.259481+00:00
-- url     : https://prove2.me/theorems/2efd0eb1-3c76-5883-9947-1aff4f97ca4a
-- title:
--   Toric Data: weil Qk Is pt
-- statement:
--   The Toric Data construction uses the weil Qk Is pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/PullTopZFConstUnit.lean#L88-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/PullTopZFConstUnit.lean#L88-L118

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_PsiWeightZeroLinearCombination
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_PullTopZFConstUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.Inh ReciprocityTheory.ChartRestriction.G.Out.InhTate ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ToricData
variable {K : Type} [CommRing K] [IsDomain K] {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
variable (q : X → (FractionRing K)ˣ)
variable (F : Type) [Field F] [Algebra (FractionRing K) F]

theorem GlobalTheory.ToricData.weilQkIs_pt {n : ℕ} (p p' : QkPt (toricPre K X q) F n) (t t') (hp : p.g = pt q F t) (hp' : p'.g = pt q F t') :
    WeilQkIs (toricPre K X q) F n p p'
      ((t (Multiplicative.ofAdd (show X from p'.y)) * (t' (Multiplicative.ofAdd (show X from p.y)))⁻¹ : Fˣ) : F) := by sorry
