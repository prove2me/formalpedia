-- Prove2me | Theorems.Thm_GlobalTheory_PushInv_exists_nhds_of_gs_eq
-- name    : GlobalTheory.PushInv.exists_nhds_of_gs_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:58:29.990797+00:00
-- url     : https://prove2.me/theorems/089ef3f5-2e4a-4322-902b-91d37897965c
-- title:
--   Push Inv: exists nhds of gs eq
-- statement:
--   The Push Inv construction uses the exists nhds of gs eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/PushInvertibleOfDensePart.lean#L81-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/PushInvertibleOfDensePart.lean#L81-L94

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsProperRestrictPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PushInvertibleOfDensePart
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory GlobalTheory.PushInv
open GlobalTheory.AbLocusPull
variable {X Y Z : Scheme.{0}}

theorem GlobalTheory.PushInv.exists_nhds_of_gs_eq {U₁ U₂ U₃ : X.Opens} {x : X} (h₁ : x ∈ U₁) (h₂ : x ∈ U₂) (h₃ : x ∈ U₃)
    (f₁ : Γ(X, U₁)) (f₂ : Γ(X, U₂)) (f₃ : Γ(X, U₃))
    (e : gs (𝟙 X) x U₁ f₁ = gs (𝟙 X) x U₂ f₂ * gs (𝟙 X) x U₃ f₃) :
    ∃ N : X.Opens, x ∈ N ∧ N ≤ U₁ ⊓ U₂ ⊓ U₃ ∧
      ∀ z ∈ N, gs (𝟙 X) z U₁ f₁ = gs (𝟙 X) z U₂ f₂ * gs (𝟙 X) z U₃ f₃ := by sorry
