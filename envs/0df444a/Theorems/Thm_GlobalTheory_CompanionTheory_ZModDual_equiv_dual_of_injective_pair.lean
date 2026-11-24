-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ZModDual_equiv_dual_of_injective_pair
-- name    : GlobalTheory.CompanionTheory.ZModDual.equiv_dual_of_injective_pair
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:24:30.140662+00:00
-- url     : https://prove2.me/theorems/7a635890-fa60-4a13-9d6a-54d71799d61a
-- title:
--   ZMod Dual: equiv dual of injective pair
-- statement:
--   The ZMod Dual construction uses the equiv dual of injective pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteDualInjectiveEquiv.lean#L28-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteDualInjectiveEquiv.lean#L28-L43

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNormalised_a407f4592f87c8cd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardDualZmodModuleEqCard
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteDualInjectiveEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZModDual

theorem GlobalTheory.CompanionTheory.ZModDual.equiv_dual_of_injective_pair :
    ∀ (n : ℕ) [NeZero n] (X Y : Type) [AddCommGroup X] [Module (ZMod n) X] [Finite X]
      [AddCommGroup Y] [Module (ZMod n) Y] [Finite Y],
      (∃ f : Y →ₗ[ZMod n] Module.Dual (ZMod n) X, Function.Injective f) →
      (∃ g : X →ₗ[ZMod n] Module.Dual (ZMod n) Y, Function.Injective g) →
      Nonempty (Y ≃ₗ[ZMod n] Module.Dual (ZMod n) X) ∧ Nat.card X = Nat.card Y := by sorry
