-- Prove2me | Theorems.Thm_GlobalTheory_ToricData_gtAct_pt
-- name    : GlobalTheory.ToricData.gtAct_pt
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:47:40.308861+00:00
-- url     : https://prove2.me/theorems/851b9972-b895-55dd-9aa3-799d0e7df116
-- title:
--   Toric Data: gt Act pt
-- statement:
--   The Toric Data construction uses the gt Act pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ZeroFLeftExt.lean#L59-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ZeroFLeftExt.lean#L59-L73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_PsiWeightZeroLinearCombination
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ZeroFLeftExt
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
variable (q : X → (FractionRing K)ˣ) (F : Type) [Field F] [Algebra (FractionRing K) F]

theorem GlobalTheory.ToricData.gtAct_pt (O : Type) [CommRing O] [StarRing O] [Module O X] (h) (a : O) (t t') :
    GtAct (toricOAct q O h) a (pt q F t) (pt q F t') ↔
      ∀ χ : X, t' (Multiplicative.ofAdd χ) = t (Multiplicative.ofAdd (star a • χ)) := by sorry
