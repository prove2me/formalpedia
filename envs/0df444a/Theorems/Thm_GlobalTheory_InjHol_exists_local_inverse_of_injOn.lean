-- Prove2me | Theorems.Thm_GlobalTheory_InjHol_exists_local_inverse_of_injOn
-- name    : GlobalTheory.InjHol.exists_local_inverse_of_injOn
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:19:26.315392+00:00
-- url     : https://prove2.me/theorems/0985fdb3-74de-4153-91ef-3de3b1a6f698
-- title:
--   Inj Hol: exists local inverse of inj On
-- statement:
--   The Inj Hol construction uses the exists local inverse of inj On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsHolomorphicLocalInverseOfInjOn.lean#L25-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsHolomorphicLocalInverseOfInjOn.lean#L25-L49

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NotInjOnOfFderivEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsHolomorphicLocalInverseOfInjOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.InjHol

theorem GlobalTheory.InjHol.exists_local_inverse_of_injOn :
    ∀ (n : ℕ) (W : Set (V n)) (g : V n → V n) (a : V n), IsOpen W → a ∈ W →
      DifferentiableOn ℂ g W → Set.InjOn g W →
      ∃ h : V n → V n, ∀ᶠ u in 𝓝 (g a), h u ∈ W ∧ g (h u) = u ∧ DifferentiableAt ℂ h u := by sorry
