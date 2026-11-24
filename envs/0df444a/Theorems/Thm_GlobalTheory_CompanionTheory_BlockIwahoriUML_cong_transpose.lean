-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BlockIwahoriUML_cong_transpose
-- name    : GlobalTheory.CompanionTheory.BlockIwahoriUML.cong_transpose
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:26:50.230039+00:00
-- url     : https://prove2.me/theorems/c16e0727-9584-411a-af81-0b83217b9cf4
-- title:
--   Block Iwahori UML: cong transpose
-- statement:
--   The Block Iwahori UML construction uses the cong transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IwahoriBlockUpperLeviLower.lean#L168-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IwahoriBlockUpperLeviLower.lean#L168-L174

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

theorem GlobalTheory.CompanionTheory.BlockIwahoriUML.cong_transpose (v : Valuation k Γ) {r : Γ} {n : ℕ} {A : Matrix (Fin n) (Fin n) k}
    (hA : Cong v r A) : Cong v r Aᵀ := by sorry
