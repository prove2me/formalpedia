-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_surjective_towerComp
-- name    : GroundTheory.Arith.SchemeCoh.surjective_towerComp
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:29:17.781909+00:00
-- url     : https://prove2.me/theorems/4be56cd7-73b2-4609-820d-416a571c2e19
-- title:
--   Scheme Coh: surjective tower Comp
-- statement:
--   The Scheme Coh construction uses the surjective tower Comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/FormalLimit.lean#L160-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/FormalLimit.lean#L160-L166

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
omit [∀ n, AddCommGroup (E n)] [∀ n, Module A (E n)] [∀ n, AddCommGroup (Q n)]
  [∀ n, Module A (Q n)]

theorem GroundTheory.Arith.SchemeCoh.surjective_towerComp (hsurj : ∀ n, Function.Surjective (τP n)) (n k : ℕ) :
    Function.Surjective (towerComp τP n k) := by sorry
