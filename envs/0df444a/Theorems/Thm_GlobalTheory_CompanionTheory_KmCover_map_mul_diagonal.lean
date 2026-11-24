-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KmCover_map_mul_diagonal
-- name    : GlobalTheory.CompanionTheory.KmCover.map_mul_diagonal
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:51:08.51482+00:00
-- url     : https://prove2.me/theorems/3e1dff7c-b8e6-4b29-a1b8-7dbe3cf9dc2a
-- title:
--   Km Cover: map mul diagonal
-- statement:
--   The Km Cover construction uses the map mul diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SolveUnitriangular.lean#L252-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SolveUnitriangular.lean#L252-L258

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUdlOfIsUnit
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SolveUnitriangular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KmCover
open Matrix

theorem GlobalTheory.CompanionTheory.KmCover.map_mul_diagonal {R K : Type} [CommRing R] [Field K] (f : R →+* K) {n : ℕ}
    (e : Fin n → K) (X Y : Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, f (X i j) * e j = e i * f (Y i j)) :
    X.map f * Matrix.diagonal e = Matrix.diagonal e * Y.map f := by sorry
