-- Prove2me | Theorems.Thm_GlobalSparseNativeWork_capacity_and_normalized_fidelity
-- name    : GlobalSparseNativeWork.capacity_and_normalized_fidelity
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T22:23:21.250843+00:00
-- url     : https://prove2.me/theorems/5ca7131e-0912-4e1a-b24e-e808cba69dca
-- title:
--   A single sparse work-tape code determines all normalized tapes
-- statement:
--   For k work tapes, a relative window of W positions on each zipper side, symbols numbered at most A, and a shared budget of K nonblank entries, the packed code type has exactly (2kW(A+1)+1)^K elements. When the tape count, zipper lengths, symbol values, and total nonblank count satisfy these bounds, equal codes imply equal lists of normalized tapes.
-- source:
--   Sparse relative work-tape profiles for the Complexitylib native machine model.

import Definitions.Def_GlobalSparseWorkTapes

open Turing.MultiTapeTM.Universal TrimmedWorkTape GlobalSparseNativeWork

theorem GlobalSparseNativeWork.capacity_and_normalized_fidelity (count window alphabet entries : ℕ) :
    (Fintype.card (GlobalSparseWorkCode count window alphabet entries) =
      (2*count*window*(alphabet+1)+1)^entries) ∧
    (∀ (xs ys : List Tape),
      GlobalSparseWorkFits count window alphabet entries xs →
      GlobalSparseWorkFits count window alphabet entries ys →
      packGlobalSparseWork count window alphabet entries xs =
        packGlobalSparseWork count window alphabet entries ys →
      xs.map normalizeTape = ys.map normalizeTape) := by sorry
