-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_range_towerComp_eq_of_exact
-- name    : GroundTheory.Arith.SchemeCoh.range_towerComp_eq_of_exact
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:52:16.394926+00:00
-- url     : https://prove2.me/theorems/2b5dbc1e-797f-5207-bc62-e34b8defec9a
-- title:
--   Scheme Coh: range tower Comp eq of exact
-- statement:
--   The Scheme Coh construction uses the range tower Comp eq of exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/FormalLimit.lean#L170-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/FormalLimit.lean#L170-L184

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_FormalLimit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
universe u
noncomputable section
variable {A : Type u} [CommRing A]
  {P E Q : ℕ → Type u} [∀ n, AddCommGroup (P n)] [∀ n, Module A (P n)]
  [∀ n, AddCommGroup (E n)] [∀ n, Module A (E n)] [∀ n, AddCommGroup (Q n)]
  [∀ n, Module A (Q n)]
  (τP : ∀ n, P (n + 1) →ₗ[A] P n) (τE : ∀ n, E (n + 1) →ₗ[A] E n) (τQ : ∀ n, Q (n + 1) →ₗ[A] Q n)
  (ι : ∀ n, P n →ₗ[A] E n) (π : ∀ n, E n →ₗ[A] Q n)
  (hι : ∀ n, (τE n).comp (ι (n + 1)) = (ι n).comp (τP n))
  (hπ : ∀ n, (τQ n).comp (π (n + 1)) = (π n).comp (τE n))
variable (hinj : ∀ n, Function.Injective (ι n))
  (hex : ∀ n, LinearMap.range (ι n) = LinearMap.ker (π n))
include hι hπ hex

theorem GroundTheory.Arith.SchemeCoh.range_towerComp_eq_of_exact (hsurj : ∀ n, Function.Surjective (τP n)) {c : ℕ}
    (hc : ∀ n, towerComp τQ n c = 0) (n k : ℕ) (hk : c ≤ k) :
    LinearMap.range (towerComp τE n k) = LinearMap.range (ι n) := by sorry
