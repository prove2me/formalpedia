-- Prove2me | Theorems.Thm_GlobalTheory_KS_Sym_Der_eq_zero
-- name    : GlobalTheory.KS.Sym.Der.eq_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:45:20.244301+00:00
-- url     : https://prove2.me/theorems/0a0d4ac6-5f41-4007-92e4-f2a1ac928450
-- title:
--   Der: eq zero
-- statement:
--   The Der construction uses the eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ConstFnCompSpMap.lean#L156-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ConstFnCompSpMap.lean#L156-L197

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstFnCompSpMap
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
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.Sym
variable {X X₂ Y Z : Scheme.{0}}

theorem GlobalTheory.KS.Sym.Der.eq_zero {h : Z ⟶ X} {T : Z.Opens} {δ : ∀ O : X.Opens, Γ(X, O) → ∀ O' : Z.Opens, Γ(Z, O')}
    (a : Der h T δ) {W : X.Opens} (hW : IsAffineOpen W) (hT : T ≤ h ⁻¹ᵁ W) (h0 : ∀ f, δ W f T = 0)
    (O : X.Opens) (f : Γ(X, O)) (O' : Z.Opens) (h₁ : O' ≤ T) (h₂ : O' ≤ h ⁻¹ᵁ O) : δ O f O' = 0 := by sorry
