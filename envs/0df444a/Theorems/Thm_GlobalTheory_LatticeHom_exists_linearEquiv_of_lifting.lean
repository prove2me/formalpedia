-- Prove2me | Theorems.Thm_GlobalTheory_LatticeHom_exists_linearEquiv_of_lifting
-- name    : GlobalTheory.LatticeHom.exists_linearEquiv_of_lifting
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:48:49.651208+00:00
-- url     : https://prove2.me/theorems/f0c5bd14-9d52-4d8f-8011-9dff26a2ecc1
-- title:
--   Lattice Hom: exists linear Equiv of lifting
-- statement:
--   The Lattice Hom construction uses the exists linear Equiv of lifting property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLinearEquivOfLifting.lean#L21-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLinearEquivOfLifting.lean#L21-L40

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ThetaUnifAVOfLaws
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLinearEquivOfLifting
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LatticeHom

theorem GlobalTheory.LatticeHom.exists_linearEquiv_of_lifting {A : Over (Sp ℂ)} [GrpObj A] {L L₁ : LB A.left} {g : ℕ}
    (u : HolUnif A L g) (v : HolUnif A L₁ g)
    (hv : ∀ (n : ℕ) (a : (Fin n → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A)), (∀ (U : A.left.Opens) (f : Γ(A.left, U)),
      IsOpen {w | w ∈ (Set.univ : Set (Fin n → ℂ)) ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U} ∧
        DifferentiableOn ℂ (fun w => valAt' (a w).left U f)
          {w | w ∈ (Set.univ : Set (Fin n → ℂ)) ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U}) → a 0 = 1 →
      ∃ G : (Fin n → ℂ) → (Fin g → ℂ), G 0 = 0 ∧ AnalyticAt ℂ G 0 ∧ ∀ᶠ w in 𝓝 0, v.ex (G w) = a w) :
    ∃ T : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ z, v.ex (T z) = u.ex z := by sorry
