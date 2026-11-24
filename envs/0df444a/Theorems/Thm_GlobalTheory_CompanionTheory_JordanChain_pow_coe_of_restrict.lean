-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_JordanChain_pow_coe_of_restrict
-- name    : GlobalTheory.CompanionTheory.JordanChain.pow_coe_of_restrict
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:53:00.059238+00:00
-- url     : https://prove2.me/theorems/97cf3ed4-22be-4b14-ae97-25ba2c5ee0b7
-- title:
--   Jordan Chain: pow coe of restrict
-- statement:
--   The Jordan Chain construction uses the pow coe of restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsChainsOfRange.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsChainsOfRange.lean#L12-L16

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsChainsOfRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.JordanChain
open Module Submodule
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

theorem GlobalTheory.CompanionTheory.JordanChain.pow_coe_of_restrict {W : Submodule K V} (f : V →ₗ[K] V) (g : W →ₗ[K] W)
    (hg : ∀ x, (g x : V) = f x) (k : ℕ) (x : W) : (((g ^ k) x : W) : V) = (f ^ k) x := by sorry
