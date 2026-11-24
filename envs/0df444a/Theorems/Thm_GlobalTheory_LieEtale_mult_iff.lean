-- Prove2me | Theorems.Thm_GlobalTheory_LieEtale_mult_iff
-- name    : GlobalTheory.LieEtale.mult_iff
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:05:05.901815+00:00
-- url     : https://prove2.me/theorems/fb59e1fb-8479-4873-81b8-6f96dae41676
-- title:
--   Lie Etale: mult iff
-- statement:
--   The Lie Etale construction uses the mult iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniqueTangentLift.lean#L71-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniqueTangentLift.lean#L71-L112

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueTangentLift
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
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.LieEtale
variable {S : Scheme.{0}} {O k : Type} {P E : Over S}

theorem GlobalTheory.LieEtale.mult_iff {A B : Over S} [GrpObj A] [GrpObj B] (ψ : A ⟶ B) [IsMonHom ψ]
    (z : P ⟶ E) (sc : k → (E ⟶ E)) (hz : ∀ c, z ≫ sc c = z)
    (a : O → (A ⟶ A)) (b : O → (B ⟶ B)) (ha : ∀ c, IsMonHom (a c))
    (hab : ∀ c, a c ≫ ψ = ψ ≫ b c) (τ : O → k)
    (H : ∀ w : E ⟶ B, z ≫ w = 1 → ∃! v : E ⟶ A, z ≫ v = 1 ∧ v ≫ ψ = w) (n : ℕ) :
    (∃ v : Fin n → (E ⟶ A), (∀ i, Eig z sc a τ (v i)) ∧ ∀ w, Eig z sc a τ w →
      ∃! c : Fin n → k, w = (List.ofFn fun i => sc (c i) ≫ v i).prod) ↔
    (∃ v : Fin n → (E ⟶ B), (∀ i, Eig z sc b τ (v i)) ∧ ∀ w, Eig z sc b τ w →
      ∃! c : Fin n → k, w = (List.ofFn fun i => sc (c i) ≫ v i).prod) := by sorry
