-- Prove2me | Theorems.Thm_GlobalTheory_linear_longExact
-- name    : GlobalTheory.linear_longExact
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:48:39.768806+00:00
-- url     : https://prove2.me/theorems/c7f1eec0-738d-5c34-903a-1d3f4d270587
-- title:
--   Global Theory: linear long Exact
-- statement:
--   The Global Theory construction uses the linear long Exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L360-L389
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L360-L389

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Module
universe t v u
noncomputable section
open GlobalTheory
variable {X : Scheme.{u}}

theorem GlobalTheory.linear_longExact {S : ShortComplex X.Modules} (hS : S.ShortExact) :
    (∀ (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)] (U : X.Opens),
      (∃ d : ∀ n, cohOn S.X₃ U n →ₗ[R] cohOn S.X₁ U (n + 1),
        (∀ n x, cohOn.toH' S.X₁ U (n + 1) (d n x) =
          SheafLES.δ.{u} (shortExact_toAbSheaf hS) n U (cohOn.toH' S.X₃ U n x)) ∧
        Function.Injective (cohOn.map R S.f U 0) ∧ ∀ n,
          Function.Exact (cohOn.map R S.f U n) (cohOn.map R S.g U n) ∧
          Function.Exact (cohOn.map R S.g U n) (d n) ∧
          Function.Exact (d n) (cohOn.map R S.f U (n + 1))) ∧
      (IsNoetherianRing R →
        (Module.Finite R (cohOn S.X₂ U 0) → Module.Finite R (cohOn S.X₁ U 0)) ∧ ∀ n,
        (Module.Finite R (cohOn S.X₁ U n) → Module.Finite R (cohOn S.X₃ U n) →
          Module.Finite R (cohOn S.X₂ U n)) ∧
        (Module.Finite R (cohOn S.X₂ U n) → Module.Finite R (cohOn S.X₁ U (n + 1)) →
          Module.Finite R (cohOn S.X₃ U n)) ∧
        (Module.Finite R (cohOn S.X₃ U n) → Module.Finite R (cohOn S.X₂ U (n + 1)) →
          Module.Finite R (cohOn S.X₁ U (n + 1))))) ∧
    ∀ (k : Type v) [Field k] [Algebra k Γ(X, ⊤)],
      (∀ n, Module.Finite k (coh S.X₁ n) → Module.Finite k (coh S.X₃ n) →
        hdim k S.X₂ n ≤ hdim k S.X₁ n + hdim k S.X₃ n) ∧
      ∀ N, (∀ i < N, Module.Finite k (coh S.X₁ i)) → (∀ i < N, Module.Finite k (coh S.X₃ i)) →
        Subsingleton (coh S.X₁ N) →
        ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * hdim k S.X₂ i =
          ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * hdim k S.X₁ i +
            ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * hdim k S.X₃ i := by sorry
