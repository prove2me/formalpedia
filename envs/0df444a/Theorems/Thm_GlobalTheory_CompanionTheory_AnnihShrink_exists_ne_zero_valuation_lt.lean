-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AnnihShrink_exists_ne_zero_valuation_lt
-- name    : GlobalTheory.CompanionTheory.AnnihShrink.exists_ne_zero_valuation_lt
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:17:34.666411+00:00
-- url     : https://prove2.me/theorems/7dd89a9f-afae-4ab5-996c-a81298fe3410
-- title:
--   Annih Shrink: exists ne zero valuation lt
-- statement:
--   The Annih Shrink construction uses the exists ne zero valuation lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LatticeAnnihilatorWithinNhds.lean#L9-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LatticeAnnihilatorWithinNhds.lean#L9-L22

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LatticeAnnihilatorWithinNhds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix ValuativeRel
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AnnihShrink

theorem GlobalTheory.CompanionTheory.AnnihShrink.exists_ne_zero_valuation_lt (k : Type) [Field k] [ValuativeRel k] [ValuativeRel.IsNontrivial k]
    (γ : ValueGroupWithZero k) (hγ : γ ≠ 0) : ∃ t : k, t ≠ 0 ∧ valuation k t < γ := by sorry
