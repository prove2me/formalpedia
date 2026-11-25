-- Prove2me | Theorems.Thm_GlobalTheory_ToricData_baseMap_pb
-- name    : GlobalTheory.ToricData.baseMap_pb
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:34:19.16361+00:00
-- url     : https://prove2.me/theorems/74038d1b-ca49-5557-bb42-0761a81d5e57
-- title:
--   Toric Data: base Map pb
-- statement:
--   The Toric Data construction uses the base Map pb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/ArcVarZpowInjective.lean#L291-L295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/ArcVarZpowInjective.lean#L291-L295

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

theorem GlobalTheory.ToricData.baseMap_pb {K' : Type} [CommRing K'] [IsDomain K'] (f : K →+* K') (q' : X → (FractionRing K')ˣ) :
    IsGrpPullback (toricPre K' X q').P.A (toricPre K X q).P.A (spMap f) (baseMap q f q') := by sorry
