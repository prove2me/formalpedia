-- Prove2me | Theorems.Thm_GlobalTheory_KS_SquareField_main
-- name    : GlobalTheory.KS.SquareField.main
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:52:43.449777+00:00
-- url     : https://prove2.me/theorems/517cc8e1-46bc-4dab-9e1f-1d16ab173385
-- title:
--   Square Field: main
-- statement:
--   The Square Field construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsLieCombZero.lean#L101-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsLieCombZero.lean#L101-L124

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueInvariantVectorFieldOfTangentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantVectorFieldsAlongGroupHomStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsLieCombZero
import Theorems.Thm_GlobalTheory_KS_InvField_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.SquareField
variable {K : Type} [Field K]

theorem GlobalTheory.KS.SquareField.main : ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] [IsCommMonObj A₀] (v : epsR K ⟶ A₀) (dd : ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)), IsTangent v → IsInvDer v dd → ∀ (n n' : A₀ ⊗ A₀ ⟶ A₀), ((n = fst A₀ A₀ ∧ n' = snd A₀ A₀) ∨ (n = snd A₀ A₀ ∧ n' = fst A₀ A₀)) → ∃ dw : ∀ O : (A₀ ⊗ A₀).left.Opens, Γ((A₀ ⊗ A₀).left, O) → Γ((A₀ ⊗ A₀).left, O), (∀ W f f', dw W (f + f') = dw W f + dw W f') ∧ (∀ W f f', dw W (f * f') = f * dw W f' + f' * dw W f) ∧ (∀ W W' (f : Γ((A₀ ⊗ A₀).left, W)), W' ≤ W → dw W' (rsT f W') = rsT (dw W f) W') ∧ (∀ W a, dw W (constFn (A₀ ⊗ A₀).hom W a) = 0) ∧ (∀ (W : A₀.left.Opens) (h : Γ(A₀.left, W)) O, O ≤ (fst A₀ A₀ * snd A₀ A₀).left ⁻¹ᵁ W → dw O (pbT (fst A₀ A₀ * snd A₀ A₀).left h O) = pbT (fst A₀ A₀ * snd A₀ A₀).left (dd W h) O) ∧ (∀ (W : A₀.left.Opens) (h : Γ(A₀.left, W)) O, O ≤ n.left ⁻¹ᵁ W → dw O (pbT n.left h O) = pbT n.left (dd W h) O) ∧ (∀ (W : A₀.left.Opens) (h : Γ(A₀.left, W)) O, O ≤ n'.left ⁻¹ᵁ W → dw O (pbT n'.left h O) = 0) := by sorry
