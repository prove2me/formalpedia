-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AnnihShrink_isCompact_box
-- name    : GlobalTheory.CompanionTheory.AnnihShrink.isCompact_box
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:17:49.08385+00:00
-- url     : https://prove2.me/theorems/97e4eaf1-c8f7-47e5-a268-a4d8c5129b3c
-- title:
--   Annih Shrink: is Compact box
-- statement:
--   The Annih Shrink construction uses the is Compact box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LatticeAnnihilatorWithinNhds.lean#L33-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LatticeAnnihilatorWithinNhds.lean#L33-L39

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
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.CompanionTheory.AnnihShrink.isCompact_box (n : ℕ) (b : k) : IsCompact (box n b : Set (Fin n → k)) := by sorry
