-- Prove2me | Theorems.Thm_GlobalTheory_EndDivisible_eq_one_of_forall_pow_dvd
-- name    : GlobalTheory.EndDivisible.eq_one_of_forall_pow_dvd
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:04:42.736921+00:00
-- url     : https://prove2.me/theorems/64bb6a76-786a-5d1f-b545-f4c1bba90ce9
-- title:
--   End Divisible: eq one of forall pow dvd
-- statement:
--   The End Divisible construction uses the eq one of forall pow dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/MemRangeOfSumEqZero.lean#L105-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/MemRangeOfSumEqZero.lean#L105-L201

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfLocalOnBase
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MemRangeOfSumEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.EndDivisible
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic TopologicalSpace

theorem GlobalTheory.EndDivisible.eq_one_of_forall_pow_dvd :
    (∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f → GeometricallyIntegral f) → (∀ (S : Scheme.{0}) (P : PolAV S) (n : ℕ), ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, (mulA P.A n).left] ![(n : ℤ) ^ 2, -1]), α.IsGen) → (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (M : LB P.A.left), M.IsLB → ∃ n : ℕ, ∀ s : Fin n → LB.Sec M, ∃ c : Fin n → Γ(Spec (CommRingCat.of K), ⊤), c ≠ 0 ∧ ∀ i, ∑ k, (P.A.hom.appLE ⊤ (M.U i) le_top).hom (c k) * (s k).f i = 0) → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (q : ℕ), 2 ≤ q → ∀ u : P.A ⟶ P.A, (∀ k : ℕ, ∃ ψ : P.A ⟶ P.A, IsMonHom ψ ∧ u = ψ ^ (q ^ k)) → u = 1 := by sorry
