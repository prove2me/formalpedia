-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMult_one_lc
-- name    : GlobalTheory.CompanionTheory.HeckeMult.one_lc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:26:30.423093+00:00
-- url     : https://prove2.me/theorems/2269c186-234f-46f7-b859-468b1a6fbc08
-- title:
--   Hecke Mult: one lc
-- statement:
--   The Hecke Mult construction uses the one lc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsUpperLower.lean#L53-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsUpperLower.lean#L53-L55

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

theorem GlobalTheory.CompanionTheory.HeckeMult.one_lc {n : ℕ} (i : Fin n) :
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (Fin.last n) i.castSucc = 0 := by sorry
