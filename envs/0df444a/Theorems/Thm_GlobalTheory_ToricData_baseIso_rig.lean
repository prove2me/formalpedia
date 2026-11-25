-- Prove2me | Theorems.Thm_GlobalTheory_ToricData_baseIso_rig
-- name    : GlobalTheory.ToricData.baseIso_rig
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:27:02.732907+00:00
-- url     : https://prove2.me/theorems/1e263e9f-2d26-4917-8fbd-9f4dad0a6b0e
-- title:
--   Toric Data: base Iso rig
-- statement:
--   The Toric Data construction uses the base Iso rig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/ArcVarZpowInjective.lean#L327-L345
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/ArcVarZpowInjective.lean#L327-L345

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_PsiWeightZeroLinearCombination
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ArcVarZpowInjective
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
variable {K' : Type} [CommRing K'] [IsDomain K']
variable (f : K →+* K') (q' : X → (FractionRing K')ˣ)

theorem GlobalTheory.ToricData.baseIso_rig (he : eSec (toricPre K' X q').P.A ≫ baseMap q f q' = spMap f ≫ eSec (toricPre K X q).P.A) :
    LB.Gen.Maps (LB.linCombIso (baseIso q f q') (K := PUnit) (fun _ => eSec (toricPre K' X q').P.A) (fun _ => 1))
      (toricPre K' X q').rig
      (rigPullOf (baseMap q f q') (spMap f) he (toricPre K X q).P.L (toricPre K X q).rig) := by sorry
