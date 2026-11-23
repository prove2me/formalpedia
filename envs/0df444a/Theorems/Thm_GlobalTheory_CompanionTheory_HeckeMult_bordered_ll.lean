-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMult_bordered_ll
-- name    : GlobalTheory.CompanionTheory.HeckeMult.bordered_ll
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:24:23.150276+00:00
-- url     : https://prove2.me/theorems/2a30d3d4-c3ea-4227-ac4d-e051d9fba2d4
-- title:
--   Hecke Mult: bordered ll
-- statement:
--   The Hecke Mult construction uses the bordered ll property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsUpperLower.lean#L40-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsUpperLower.lean#L40-L41

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

theorem GlobalTheory.CompanionTheory.HeckeMult.bordered_ll :
    bordered M c r d (Fin.last n) (Fin.last n) = d := by sorry
