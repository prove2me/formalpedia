-- Prove2me | Theorems.Thm_GlobalTheory_ToricData_isIota_pt
-- name    : GlobalTheory.ToricData.isIota_pt
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T14:41:02.715711+00:00
-- url     : https://prove2.me/theorems/d38ac380-a2e9-460d-8ddb-da90a6ef0b58
-- title:
--   Toric Data: is Iota pt
-- statement:
--   The Toric Data construction uses the is Iota pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ZeroFLeftExt.lean#L52-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ZeroFLeftExt.lean#L52-L57

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

theorem GlobalTheory.ToricData.isIota_pt (y : X) (t) : GtPtF.IsIota (D := toricPre K X q) y (pt q F t) ↔
    ∀ χ, (t (Multiplicative.ofAdd χ) : F) = algebraMap (FractionRing K) F (polar q y χ) := by sorry
