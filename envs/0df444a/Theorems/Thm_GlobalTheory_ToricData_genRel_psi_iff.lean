-- Prove2me | Theorems.Thm_GlobalTheory_ToricData_genRel_psi_iff
-- name    : GlobalTheory.ToricData.genRel_psi_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:39:37.99721+00:00
-- url     : https://prove2.me/theorems/6b8f4cfa-d1f4-5a63-8078-99637becded6
-- title:
--   Toric Data: gen Rel psi iff
-- statement:
--   The Toric Data construction uses the gen Rel psi iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/ArcVarZpowInjective.lean#L409-L418
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/ArcVarZpowInjective.lean#L409-L418

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

theorem GlobalTheory.ToricData.genRel_psi_iff
    (hF : ∀ x, algebraMap (FractionRing K) F (algebraMap K _ x) = algebraMap (FractionRing K') F (algebraMap K' _ (f x)))
    (y' y : X) (x : F) :
    GenRel (baseIso q f q') (LB.pullGen _ _ _ ((toricPre K' X q').psi y') (jFK (R := K') F))
        (LB.pullGen _ _ _ ((toricPre K X q).psi y) (jFK (R := K) F)) x ↔
      algebraMap (FractionRing K') F (q' y') = x * algebraMap (FractionRing K) F (q y) := by sorry
