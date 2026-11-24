-- Prove2me | Theorems.Thm_GlobalTheory_KS_Primitive_exists_split
-- name    : GlobalTheory.KS.Primitive.exists_split
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:45:04.131795+00:00
-- url     : https://prove2.me/theorems/b7fff528-043a-4b8e-a17f-ddb3a8e9203e
-- title:
--   Primitive: exists split
-- statement:
--   The Primitive construction uses the exists split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CechPrimitive.lean#L65-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CechPrimitive.lean#L65-L84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenInfOfIsSeparated
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CechPrimitive
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
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.Primitive
open GlobalTheory.KuennethOne
variable {T Z A : Scheme.{0}} {I : Type} {U : I → A.Opens} {c : C1 U}

theorem GlobalTheory.KS.Primitive.exists_split (hc : IsCoc U c) (f g : T ⟶ A) {i₀ : I} (hg : ⊤ ≤ g ⁻¹ᵁ U i₀) {J : Type}
    (i₁ i₂ i₃ : J → I) (N : J → T.Opens) (h₁ : ∀ a, N a ≤ f ⁻¹ᵁ U (i₁ a))
    (h₂ : ∀ a, N a ≤ f ⁻¹ᵁ U (i₂ a)) (h₃ : ∀ a, N a ≤ g ⁻¹ᵁ U (i₃ a)) :
    ∃ ψ : ∀ a, Γ(T, N a), ∀ a b (M : T.Opens) (ha : M ≤ N a) (hb : M ≤ N b),
      pbT f (c (i₁ a) (i₁ b)) M - pbT f (c (i₂ a) (i₂ b)) M - pbT g (c (i₃ a) (i₃ b)) M =
        rs ha (ψ a) - rs hb (ψ b) := by sorry
