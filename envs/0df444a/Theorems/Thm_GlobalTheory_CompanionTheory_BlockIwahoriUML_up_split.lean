-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BlockIwahoriUML_up_split
-- name    : GlobalTheory.CompanionTheory.BlockIwahoriUML.up_split
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:27:07.397169+00:00
-- url     : https://prove2.me/theorems/db11bd6f-04cd-4a7e-8478-64359487e3b7
-- title:
--   Block Iwahori UML: up split
-- statement:
--   The Block Iwahori UML construction uses the up split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IwahoriBlockUpperLeviLower.lean#L94-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IwahoriBlockUpperLeviLower.lean#L94-L166

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUdlOfIsUnit
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsPrincipalCongruence
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriBlockUpperLeviLower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BlockIwahoriUML
variable {k Γ : Type*} [Field k] [LinearOrderedCommGroupWithZero Γ]

theorem GlobalTheory.CompanionTheory.BlockIwahoriUML.up_split (v : Valuation k Γ) {r : Γ} (hr : r < 1) {n : ℕ} (β : Fin n → ℕ)
    (hβ : Monotone β) (u : Matrix (Fin n) (Fin n) k) (hu : Cong v r u)
    (hu0 : ∀ i j, j < i → u i j = 0) (hu1 : ∀ i, u i i = 1) :
    ∃ a m : Matrix (Fin n) (Fin n) k, a.det = 1 ∧ m.det = 1 ∧ Cong v r a ∧ Cong v r m ∧
      (∀ i j, β j ≤ β i → a i j = (1 : Matrix (Fin n) (Fin n) k) i j) ∧
      (∀ i j, β i ≠ β j → m i j = 0) ∧ u = a * m := by sorry
