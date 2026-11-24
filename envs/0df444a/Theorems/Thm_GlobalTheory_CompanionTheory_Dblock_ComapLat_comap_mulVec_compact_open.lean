-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Dblock_ComapLat_comap_mulVec_compact_open
-- name    : GlobalTheory.CompanionTheory.Dblock.ComapLat.comap_mulVec_compact_open
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:35:07.752129+00:00
-- url     : https://prove2.me/theorems/3e75eff9-c592-4af3-a157-0a39e714862c
-- title:
--   Comap Lat: comap mul Vec compact open
-- statement:
--   The Comap Lat construction uses the comap mul Vec compact open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ComapMulVecCompactOpen.lean#L7-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ComapMulVecCompactOpen.lean#L7-L29

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ComapMulVecCompactOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Dblock GlobalTheory.CompanionTheory.Dblock.ComapLat

theorem GlobalTheory.CompanionTheory.Dblock.ComapLat.comap_mulVec_compact_open : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (g : Matrix (Fin n) (Fin n) k), IsUnit g → ∀ A : AddSubgroup (Fin n → k), IsCompact (A : Set (Fin n → k)) → IsOpen (A : Set (Fin n → k)) → IsCompact ((A.comap (Matrix.mulVecLin g).toAddMonoidHom : AddSubgroup (Fin n → k)) : Set (Fin n → k)) ∧ IsOpen ((A.comap (Matrix.mulVecLin g).toAddMonoidHom : AddSubgroup (Fin n → k)) : Set (Fin n → k)) := by sorry
