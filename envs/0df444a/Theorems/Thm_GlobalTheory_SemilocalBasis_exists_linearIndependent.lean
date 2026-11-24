-- Prove2me | Theorems.Thm_GlobalTheory_SemilocalBasis_exists_linearIndependent
-- name    : GlobalTheory.SemilocalBasis.exists_linearIndependent
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:53:56.461797+00:00
-- url     : https://prove2.me/theorems/962f3e5c-7b3c-4be9-8aa8-eabfeca68dcd
-- title:
--   Semilocal Basis: exists linear Independent
-- statement:
--   The Semilocal Basis construction uses the exists linear Independent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsBasisMemOfSpanEqTopOfSemilocal.lean#L63-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsBasisMemOfSpanEqTopOfSemilocal.lean#L63-L121

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsBasisMemOfSpanEqTopOfSemilocal
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
open GlobalTheory
open GlobalTheory.SemilocalBasis
open scoped Pointwise

theorem GlobalTheory.SemilocalBasis.exists_linearIndependent {A B M : Type*} [CommRing A] [IsLocalRing A]
    [Infinite (IsLocalRing.ResidueField A)] [CommRing B] [Algebra A B]
    [Finite (MaximalSpectrum B)] [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    {n : ℕ} (e : Module.Basis (Fin n) B M) (N : Submodule A M)
    (hm : ∀ m : MaximalSpectrum B,
      (IsLocalRing.maximalIdeal A).map (algebraMap A B) ≤ m.asIdeal)
    (hN : Submodule.span B (N : Set M) = ⊤) (k : ℕ) (hk : k ≤ n) :
    ∃ v : Fin k → M, (∀ i, v i ∈ N) ∧ ∀ m : MaximalSpectrum B,
      LinearIndependent (B ⧸ m.asIdeal) (fun i => red e m.asIdeal (v i)) := by sorry
