-- Prove2me | Theorems.Thm_GlobalTheory_exists_equivariant_fun_on_spanning_families
-- name    : GlobalTheory.exists_equivariant_fun_on_spanning_families
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:32:45.139992+00:00
-- url     : https://prove2.me/theorems/3703d8a5-1db2-4825-b3e8-0715388eb262
-- title:
--   Global Theory: exists equivariant fun on spanning families
-- statement:
--   The Global Theory construction uses the exists equivariant fun on spanning families property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsEquivariantFunOnSpanningFamilies.lean#L19-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsEquivariantFunOnSpanningFamilies.lean#L19-L87

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_NormsFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegPFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegQFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LiftLaSpec
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsGenFrGenFr
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ChartDirectionsIntegral
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HalvesFreeAndAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsEquivariantFunOnSpanningFamilies
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open GlobalTheory

theorem GlobalTheory.exists_equivariant_fun_on_spanning_families {R M G F : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Group G] [Field F] {r n : ℕ} (hrn : r ≤ n)
    (h0 : ∃ x₀ : Fin r → M, Submodule.span R (Set.range x₀) = ⊤)
    (h1 : ∀ x x' : Fin r → M, Submodule.span R (Set.range x) = ⊤ → Submodule.span R (Set.range x') = ⊤ →
      ∃! g : M ≃ₗ[R] M, ∀ b, g (x b) = x' b)
    (adj : (M ≃ₗ[R] M) → G) (hadj : ∀ g g', adj (g * g') = adj g' * adj g) (ψ : G →* Fˣ) :
    ∃ (ph : (Fin n → M) → F) (x₀ : Fin n → M),
      (∀ x x' : Fin n → M, (∀ b : Fin n, b.val < r → x b = x' b) → ph x = ph x') ∧
      (∀ x, ph x ≠ 0 → Submodule.span R (x '' {b | b.val < r}) = ⊤) ∧
      (∀ (kst : M ≃ₗ[R] M) x, ph (fun b => kst (x b)) = (((ψ (adj kst))⁻¹ : Fˣ) : F) * ph x) ∧
      ph x₀ = 1 ∧ Submodule.span R (x₀ '' {b | b.val < r}) = ⊤ := by sorry
