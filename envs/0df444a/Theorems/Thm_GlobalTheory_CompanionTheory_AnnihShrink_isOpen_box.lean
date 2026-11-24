-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AnnihShrink_isOpen_box
-- name    : GlobalTheory.CompanionTheory.AnnihShrink.isOpen_box
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:17:51.190851+00:00
-- url     : https://prove2.me/theorems/dc2003c2-f0e6-4bab-921f-ccd8b129ab49
-- title:
--   Annih Shrink: is Open box
-- statement:
--   The Annih Shrink construction uses the is Open box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LatticeAnnihilatorWithinNhds.lean#L41-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LatticeAnnihilatorWithinNhds.lean#L41-L49

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

theorem GlobalTheory.CompanionTheory.AnnihShrink.isOpen_box (n : ℕ) (b : k) (hb : b ≠ 0) : IsOpen (box n b : Set (Fin n → k)) := by sorry
