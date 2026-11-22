-- Prove2me | Theorems.Thm_LinearSetReconciliation327_Main_p21_scratch_bounds
-- name    : LinearSetReconciliation327.Main.p21_scratch_bounds
-- status  : Proved
-- author  : @djwj233
-- created : 2026-11-21T12:33:12.213511+00:00
-- url     : https://prove2.me/theorems/2a067ef6-8e71-416f-ab62-005240318865
-- title:
--   Pinsketch decoder: the key-solver, root-search and verifier frames lie inside the decoder scratch
-- statement:
--   **The three stage frames of Proposition 2.1 never touch a word at or above `decoderAllocEnd t`.**  For $t\ge 1$: every address writable by the key-solver stage (`solverInitWritable t`) is below `decoderAllocEnd t`; every address writable by the root-search stage, at the concrete row/queue geometry $(R,U,D,C,TB,Q_0,Q_1,B)=(\texttt{rowBase}\,0,6,1,7,4,\texttt{queue}_0,\texttt{queue}_1,\texttt{outputBase})$ of the decoder, is below it; every address writable by the verification stage at $V=\texttt{decoderVerifyBase } t$ is below it; and the saved syndrome block $[\texttt{decoderSavedBase } t,\ \texttt{decoderSavedBase } t+2t)$ ends at or below it.  Consequently each published stage frame preserves the zero-ness of $[\texttt{decoderAllocEnd } t,\infty)$.
-- source:
--   arXiv:2611.11409, Section 2.2 (Pinsketch, PDF p.10): the address layout of the Proposition 2.1 decoder (`decoderSavedBase`, `decoderRowBase`, `decoderQueue0/1`, `decoderOutputBase`, `decoderVerifyBase`).

import Definitions.Def_LinearSetReconciliation327_Main_DecoderLemmas

set_option autoImplicit false

open Finset

theorem LinearSetReconciliation327.Main.p21_scratch_bounds (t : ℕ) (ht : 1 ≤ t) :
    (∀ addr, solverInitWritable t addr → addr < decoderAllocEnd t) ∧
    (∀ addr, rootSearchWritable (decoderRowBase t 0) (decoderRowBase t 6) (decoderRowBase t 1)
        (decoderRowBase t 7) (decoderRowBase t 4) (decoderCapacity t) (decoderQueue0 t)
        (decoderQueue1 t) (decoderOutputBase t) t addr → addr < decoderAllocEnd t) ∧
    (∀ addr, verifierWritable (decoderVerifyBase t) (2 * t) addr → addr < decoderAllocEnd t) ∧
    decoderSavedBase t + 2 * t ≤ decoderAllocEnd t := by sorry
