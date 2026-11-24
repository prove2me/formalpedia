-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BlockIwahoriUML_blockDiag_mul
-- name    : GlobalTheory.CompanionTheory.BlockIwahoriUML.blockDiag_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:27:01.707654+00:00
-- url     : https://prove2.me/theorems/39e9833b-a01e-4fc1-90ee-bda9d3e47ad8
-- title:
--   Block Iwahori UML: block Diag mul
-- statement:
--   The Block Iwahori UML construction uses the block Diag mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IwahoriBlockUpperLeviLower.lean#L180-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IwahoriBlockUpperLeviLower.lean#L180-L188

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

theorem GlobalTheory.CompanionTheory.BlockIwahoriUML.blockDiag_mul {n : ℕ} (β : Fin n → ℕ) {A B : Matrix (Fin n) (Fin n) k}
    (hA : ∀ i j, β i ≠ β j → A i j = 0) (hB : ∀ i j, β i ≠ β j → B i j = 0) :
    ∀ i j, β i ≠ β j → (A * B) i j = 0 := by sorry
