-- Prove2me | Theorems.Thm_GlobalTheory_T_isCompact_isOpen_comap_mulVecLin
-- name    : GlobalTheory.T.isCompact_isOpen_comap_mulVecLin
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:48:01.513587+00:00
-- url     : https://prove2.me/theorems/902b758c-47a3-485e-943e-9822f0f1b1fe
-- title:
--   T: is Compact is Open comap mul Vec Lin
-- statement:
--   The T construction uses the is Compact is Open comap mul Vec Lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ComapMulVecCompactOpenStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ComapMulVecCompactOpenStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ComapMulVecCompactOpen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ComapMulVecCompactOpenStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isCompact_isOpen_comap_mulVecLin : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (g : Matrix (Fin n) (Fin n) k), IsUnit g → ∀ A : AddSubgroup (Fin n → k), IsCompact (A : Set (Fin n → k)) → IsOpen (A : Set (Fin n → k)) → IsCompact ((A.comap (Matrix.mulVecLin g).toAddMonoidHom : AddSubgroup (Fin n → k)) : Set (Fin n → k)) ∧ IsOpen ((A.comap (Matrix.mulVecLin g).toAddMonoidHom : AddSubgroup (Fin n → k)) : Set (Fin n → k)) := by sorry
