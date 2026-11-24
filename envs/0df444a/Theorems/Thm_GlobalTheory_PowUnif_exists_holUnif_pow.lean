-- Prove2me | Theorems.Thm_GlobalTheory_PowUnif_exists_holUnif_pow
-- name    : GlobalTheory.PowUnif.exists_holUnif_pow
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:53:14.48854+00:00
-- url     : https://prove2.me/theorems/c7641ac9-b84a-4d02-9325-408647e987d8
-- title:
--   Pow Unif: exists hol Unif pow
-- statement:
--   The Pow Unif construction uses the exists hol Unif pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsHolomorphicUniformisationPowerThetaKeyDatu.lean#L383-L441
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsHolomorphicUniformisationPowerThetaKeyDatu.lean#L383-L441

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsHolomorphicUniformisationPowerThetaKeyDatu
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.PowUnif

theorem GlobalTheory.PowUnif.exists_holUnif_pow : ∀ (x y : KeyIn ℂ) (j : ℕ) (u : HolUnif x.P.A x.P.L x.P.g) (θ : (Fin x.P.g → ℂ) → ℂ) (W : Matrix (Fin x.P.g) (Fin x.P.g) ℂ), GlobalTheory.KeyPow.IsKeyPow y x j → u.IsRig x.rig → u.IsFn x.th θ → (∀ i, u.IsDiff (W i) (x.v i)) → ∃ (e : Fin j × Fin x.P.g ≃ Fin y.P.g) (u' : HolUnif y.P.A y.P.L y.P.g), (∀ z, z ∈ u'.Λ ↔ ∀ i, (fun k => z (e (i, k))) ∈ u.Λ) ∧ u'.IsRig y.rig ∧ u'.IsFn y.th (fun z => ∏ i, θ (fun k => z (e (i, k)))) ∧ ∀ p, u'.IsDiff (fun q => if (e.symm p).1 = (e.symm q).1 then W (e.symm p).2 (e.symm q).2 else 0) (y.v p) := by sorry
