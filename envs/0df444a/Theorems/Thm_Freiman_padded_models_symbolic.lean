-- Prove2me | Theorems.Thm_Freiman_padded_models_symbolic
-- name    : Freiman.padded_models_symbolic
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:53:38.700695+00:00
-- url     : https://prove2.me/theorems/0bfa34ba-57ea-46b5-bed7-cb0b14badcc4
-- title:
--   padded models symbolic
-- statement:
--   For a family of finite models padded by a fixed digit, assume a common finite alphabet, convergence of the central values to t, a uniform local upper bound t+εj with εj→0, and constant-word background at most t. Concatenation realizes t in the symbolic Lagrange spectrum; the existing symbolic equality later transfers it to the classical spectrum.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.6, Lemma 1.11 (found:padded-models), padding and finite-window proof.

import Definitions.Def_Freiman_paddedCopies
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Topology.Instances.Real.Lemmas

open Freiman

theorem Freiman.padded_models_symbolic (a : ℕ → ℤ → ℕ+) (d : ℕ+) (t : ℝ) (ε : ℕ → ℝ)
    (halphabet : ∃ M : ℕ, ∀ j : ℕ, ∀ i : ℤ, (a j i : ℕ) ≤ M)
    (hpad : ∀ j : ℕ, ∀ i : ℤ, j < i.natAbs → a j i = d)
    (hcentral : Filter.Tendsto (fun j : ℕ => localValue (a j) 0) Filter.atTop (nhds t))
    (hbound : ∀ j : ℕ, ∀ i : ℤ, localValue (a j) i ≤ t + ε j)
    (heps : Filter.Tendsto ε Filter.atTop (nhds 0))
    (hbackground : Real.sqrt ((((d : ℕ) : ℝ) ^ 2) + 4) ≤ t) :
    t ∈ symbolicLagrangeSpectrum := by sorry
