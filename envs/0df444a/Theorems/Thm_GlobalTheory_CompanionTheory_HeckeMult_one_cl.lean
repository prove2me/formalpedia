-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMult_one_cl
-- name    : GlobalTheory.CompanionTheory.HeckeMult.one_cl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:26:23.852775+00:00
-- url     : https://prove2.me/theorems/8ec7c0d5-8583-4e49-b9c1-cd8a0c72b9f2
-- title:
--   Hecke Mult: one cl
-- statement:
--   The Hecke Mult construction uses the one cl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsUpperLower.lean#L49-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsUpperLower.lean#L49-L51

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUpperLower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeMult
variable {R : Type} [CommRing R]

theorem GlobalTheory.CompanionTheory.HeckeMult.one_cl {n : ℕ} (i : Fin n) :
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i.castSucc (Fin.last n) = 0 := by sorry
