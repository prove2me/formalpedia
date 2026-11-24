-- Prove2me | Theorems.Thm_GlobalTheory_T_finite_dual_injective_equiv
-- name    : GlobalTheory.T.finite_dual_injective_equiv
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:39:24.4543+00:00
-- url     : https://prove2.me/theorems/7dbe28c3-aa49-4782-9d0c-6610c7aed3fe
-- title:
--   T: finite dual injective equiv
-- statement:
--   The T construction uses the finite dual injective equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteDualInjectiveEquivStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteDualInjectiveEquivStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteDualInjectiveEquiv
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNormalised_a407f4592f87c8cd
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteDualInjectiveEquivStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.finite_dual_injective_equiv : ∀ (n : ℕ) [NeZero n] (X Y : Type) [AddCommGroup X] [Module (ZMod n) X] [Finite X] [AddCommGroup Y] [Module (ZMod n) Y] [Finite Y], (∃ f : Y →ₗ[ZMod n] Module.Dual (ZMod n) X, Function.Injective f) → (∃ g : X →ₗ[ZMod n] Module.Dual (ZMod n) Y, Function.Injective g) → Nonempty (Y ≃ₗ[ZMod n] Module.Dual (ZMod n) X) ∧ Nat.card X = Nat.card Y := by sorry
