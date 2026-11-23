-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMult_bordered_lc
-- name    : GlobalTheory.CompanionTheory.HeckeMult.bordered_lc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:24:24.316019+00:00
-- url     : https://prove2.me/theorems/9a1695de-1303-4bd9-9094-82ec45b063ed
-- title:
--   Hecke Mult: bordered lc
-- statement:
--   The Hecke Mult construction uses the bordered lc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsUpperLower.lean#L38-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsUpperLower.lean#L38-L39

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

theorem GlobalTheory.CompanionTheory.HeckeMult.bordered_lc (j : Fin n) :
    bordered M c r d (Fin.last n) j.castSucc = r j := by sorry
