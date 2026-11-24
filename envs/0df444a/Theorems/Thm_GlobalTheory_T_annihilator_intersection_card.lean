-- Prove2me | Theorems.Thm_GlobalTheory_T_annihilator_intersection_card
-- name    : GlobalTheory.T.annihilator_intersection_card
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:26:12.598292+00:00
-- url     : https://prove2.me/theorems/e871e8d6-d3df-4af6-9a6e-7869ec31fc30
-- title:
--   T: annihilator intersection card
-- statement:
--   The T construction uses the annihilator intersection card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AnnihilatorIntersectionCardStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AnnihilatorIntersectionCardStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AnnihilatorIntersectionCard
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AnnihilatorIntersectionCardStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.annihilator_intersection_card : ∀ (n : ℕ) [NeZero n] (X Y : Type) [AddCommGroup X] [Module (ZMod n) X] [Finite X] [AddCommGroup Y] [Module (ZMod n) Y] [Finite Y] (B : Y →ₗ[ZMod n] X →ₗ[ZMod n] ZMod n), Function.Injective B → Function.Injective B.flip → ∀ I L : Submodule (ZMod n) X, Nat.card ↥((⨅ x ∈ I, LinearMap.ker (B.flip x)) ⊓ (⨅ x ∈ L, LinearMap.ker (B.flip x))) * Nat.card ↥I * Nat.card ↥L = Nat.card X * Nat.card ↥(I ⊓ L) := by sorry
