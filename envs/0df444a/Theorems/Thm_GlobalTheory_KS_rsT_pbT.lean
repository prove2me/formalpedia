-- Prove2me | Theorems.Thm_GlobalTheory_KS_rsT_pbT
-- name    : GlobalTheory.KS.rsT_pbT
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:46:51.938188+00:00
-- url     : https://prove2.me/theorems/7cd6b4da-03e9-434e-a86d-d9a4ad085a3d
-- title:
--   KS: rs T pb T
-- statement:
--   The KS construction uses the rs T pb T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/LeISupInfPreimage.lean#L78-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/LeISupInfPreimage.lean#L78-L81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
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
open GlobalTheory GlobalTheory.KS
variable {Y Z : Scheme.{0}}

theorem GlobalTheory.KS.rsT_pbT (f : Z ⟶ Y) {O₀ : Y.Opens} {O₁ O₂ : Z.Opens} (h₁ : O₁ ≤ f ⁻¹ᵁ O₀) (h₂ : O₂ ≤ O₁)
    (s : Γ(Y, O₀)) : rsT (pbT f s O₁) O₂ = pbT f s O₂ := by sorry
