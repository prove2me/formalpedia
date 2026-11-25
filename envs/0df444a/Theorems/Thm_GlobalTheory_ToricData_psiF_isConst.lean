-- Prove2me | Theorems.Thm_GlobalTheory_ToricData_psiF_isConst
-- name    : GlobalTheory.ToricData.psiF_isConst
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:39:14.034382+00:00
-- url     : https://prove2.me/theorems/a4610c79-36e3-5ddd-89e5-4c772eab7e50
-- title:
--   Toric Data: psi F is Const
-- statement:
--   The Toric Data construction uses the psi F is Const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/ArcVarZpowInjective.lean#L404-L407
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/ArcVarZpowInjective.lean#L404-L407

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
variable (F : Type) [Field F] [Algebra (FractionRing K') F] [Algebra (FractionRing K) F]
omit [Algebra (FractionRing K') F]

theorem GlobalTheory.ToricData.psiF_isConst (y : X) :
    IsConst (LB.pullGen _ _ _ ((toricPre K X q).psi y) (jFK (R := K) F))
      (unitOn (Units.map (algebraMap (FractionRing K) F).toMonoidHom (q y))) := by sorry
