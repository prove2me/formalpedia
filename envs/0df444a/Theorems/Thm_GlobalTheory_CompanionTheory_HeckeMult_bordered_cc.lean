-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMult_bordered_cc
-- name    : GlobalTheory.CompanionTheory.HeckeMult.bordered_cc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:24:21.662072+00:00
-- url     : https://prove2.me/theorems/998f55b4-5abf-47e6-8d5b-67fa98ecbdd9
-- title:
--   Hecke Mult: bordered cc
-- statement:
--   The Hecke Mult construction uses the bordered cc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsUpperLower.lean#L34-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsUpperLower.lean#L34-L35

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
variable {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (c r : Fin n → R) (d : R)

theorem GlobalTheory.CompanionTheory.HeckeMult.bordered_cc (i j : Fin n) :
    bordered M c r d i.castSucc j.castSucc = M i j := by sorry
