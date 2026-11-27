-- Prove2me | Theorems.Thm_GRH_unconditional_logarithmic_saving_in_reduced_moebius_progressions
-- name    : GRH.unconditional_logarithmic_saving_in_reduced_moebius_progressions
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-27T06:47:40.185455+00:00
-- url     : https://prove2.me/theorems/8de0bd12-ab77-4008-b29b-56a32691f41b
-- title:
--   One logarithm of cancellation for the Möbius sum in every reduced residue class
-- statement:
--   For every fixed positive q there is C(q) such that for all reduced residues a and all N, the log-weighted Möbius sum has absolute value at most C(q)N and the ordinary Möbius sum has absolute value at most C(q)N/(1+log(N+1)).
-- source:
--   Unconditional fixed-modulus estimates for the centered Möbius progression sum in https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 . Coprime reciprocal-sum input https://prove2.me/submissions/e110685c-05e3-418b-9139-db1604ac9ee5 .

import Definitions.Def_GRH_LogarithmicMoebius

open Finset Filter Topology GRH.LogarithmicMoebius

theorem GRH.unconditional_logarithmic_saving_in_reduced_moebius_progressions (q : ℕ) [NeZero q] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : (ZMod q)ˣ) (N : ℕ),
      |residueLog (a : ZMod q) N| ≤ C*(N:ℝ) ∧ |residue (a : ZMod q) N| *scale N ≤ C*(N:ℝ) := by sorry
