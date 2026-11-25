-- Prove2me | Theorems.Thm_GlobalTheory_ToricData_hom_eq_iff
-- name    : GlobalTheory.ToricData.hom_eq_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:49:17.521804+00:00
-- url     : https://prove2.me/theorems/34ed88df-1b9d-5ca6-a56a-3f447f8a2c3f
-- title:
--   Toric Data: hom eq iff
-- statement:
--   The Toric Data construction uses the hom eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ZeroFLeftExt.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ZeroFLeftExt.lean#L15-L17

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
omit [Module.Free ℤ X] [Module.Finite ℤ X]

theorem GlobalTheory.ToricData.hom_eq_iff {F : Type} [Field F] {t t' : Multiplicative X →* Fˣ} :
    (∀ χ : X, t (Multiplicative.ofAdd χ) = t' (Multiplicative.ofAdd χ)) ↔ t = t' := by sorry
