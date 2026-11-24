-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_IndexDuality_relIndex_le_of_pairing
-- name    : GlobalTheory.CompanionTheory.IndexDuality.relIndex_le_of_pairing
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:48:29.115817+00:00
-- url     : https://prove2.me/theorems/9d323381-0860-4a1a-9660-c5436ff2195d
-- title:
--   Index Duality: rel Index le of pairing
-- statement:
--   The Index Duality construction uses the rel Index le of pairing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RelIndexAnnihilatorsDuality.lean#L11-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RelIndexAnnihilatorsDuality.lean#L11-L86

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RelIndexOpenCompactNeZero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsCharacterSeparatingLattice
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RelIndexAnnihilatorsDuality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.IndexDuality

theorem GlobalTheory.CompanionTheory.IndexDuality.relIndex_le_of_pairing {X Y : Type} [AddCommGroup X] [AddCommGroup Y]
    (b : X → Y → Circle)
    (hl : ∀ x x' y, b (x + x') y = b x y * b x' y)
    (hr : ∀ x y y', b x (y + y') = b x y * b x y')
    (H₀ H : AddSubgroup Y) (R₀ R : AddSubgroup X)
    (hfin : H₀.relIndex H ≠ 0)
    (hann : ∀ x ∈ R₀, ∀ y ∈ H₀, b x y = 1)
    (hsep : ∀ x ∈ R₀, (∀ y ∈ H, b x y = 1) → x ∈ R) :
    R.relIndex R₀ ≠ 0 ∧ R.relIndex R₀ ≤ H₀.relIndex H := by sorry
