-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_towerLimitEquivOfExact_apply
-- name    : GroundTheory.Arith.SchemeCoh.towerLimitEquivOfExact_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:52:59.956785+00:00
-- url     : https://prove2.me/theorems/07923f09-3f6b-45e3-8f9c-e6f667d74f19
-- title:
--   Scheme Coh: tower Limit Equiv Of Exact apply
-- statement:
--   The Scheme Coh construction uses the tower Limit Equiv Of Exact apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/FormalLimit.lean#L153-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/FormalLimit.lean#L153-L155

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

theorem GroundTheory.Arith.SchemeCoh.towerLimitEquivOfExact_apply {c : ℕ} (hc : ∀ n, towerComp τQ n c = 0)
    (x : towerLimit τP) (n : ℕ) :
    (towerLimitEquivOfExact τP τE τQ ι π hι hπ hinj hex hc x).1 n = ι n (x.1 n) := by sorry
