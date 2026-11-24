-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_GapOpCount_pairMap_range
-- name    : GlobalTheory.CompanionTheory.GapOpCount.pairMap_range
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:42:43.534528+00:00
-- url     : https://prove2.me/theorems/4272d39c-81a8-4b62-901c-10a6e88a272f
-- title:
--   Gap Op Count: pair Map range
-- statement:
--   The Gap Op Count construction uses the pair Map range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardTwoAffineHyperplanes.lean#L12-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardTwoAffineHyperplanes.lean#L12-L41

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemRiemannRochSpaceIffRegularAtEverywhere
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardTwoAffineHyperplanes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GapOpCount

theorem GlobalTheory.CompanionTheory.GapOpCount.pairMap_range {k : Type} [Field k] {n : ℕ} (a b : Fin (n + 1) → k)
    (ha : a ≠ 0) (hb : ∀ s : k, b ≠ s • a) : LinearMap.range (pairMap a b) = ⊤ := by sorry
