-- Prove2me | Theorems.Thm_LefebvreVariations_perfect_code_quaternary_length_five
-- name    : LefebvreVariations.perfect_code_quaternary_length_five
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T01:03:34.485443+00:00
-- url     : https://prove2.me/theorems/23d1a7f6-0d58-4e92-aa90-bd7f2db07773
-- title:
--   Lefebvre's variations, No. 116 — on a theme by Richard Hamming: a perfect one-error-correcting code over four letters of length five
-- statement:
--   There is a set $C\subseteq\{0,\dots,3\}^{5}$ of words of length $5$ over an alphabet of $4$ letters such that any two distinct words differ in at least $3$ positions, and the Hamming balls of radius $1$ around the words of $C$ cover the whole space:
--   $$
--   4^{5}\le |C|\,\bigl(1+5(4-1)\bigr).
--   $$
--   Since the balls are disjoint, this means $C$ is a perfect $1$-error-correcting code, $|C|=4^{3}$ (the Hamming code over GF(4) of length 5).
--
--   **Formalization Note** This is the case $n=5$, $q=4$ of the existence half of the platform's `perfect_1_error_correcting_code`: words are functions `Fin 5 → Fin 4`, the distance is `∑ i, if x i ≠ y i then 1 else 0`, and the covering inequality is `(Finset.univ).card ≤ C.card * (1 + 5 * (4 - 1))`.
--
--   **Why this is a variation.** A variation on the platform's open `perfect_1_error_correcting_code`: the existence half at the single size n = 5, q = 4, where it is a classical Hamming code. The general classification (for example q = 6) remains open in the parent.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   The Hamming code over GF(4) of length 5 (64 words, minimum distance 3). Parent: classification of perfect 1-error-correcting codes, on the platform as `perfect_1_error_correcting_code` (open). Hamming, Error detecting and error correcting codes, Bell System Tech. J. 29 (1950) 147-160 (cited from memory). The existence statement itself was verified here by explicit construction (parity-check matrix) and computer check of minimum distance and size.

import Mathlib

namespace LefebvreVariations

/-- A perfect 1-error-correcting code of length `5` over an alphabet of size `4` exists (the Hamming code over GF(4) of length 5). Source: R. W. Hamming, Error detecting and error correcting codes, Bell System Tech. J. 29 (1950) 147-160; Hamming codes over GF(q): MacWilliams and Sloane, The Theory of Error-Correcting Codes, Ch. 7 (cited from memory). -/
theorem perfect_code_quaternary_length_five :
    ∃ (C : Finset (Fin 5 → Fin 4)),
      (∀ x ∈ C, ∀ y ∈ C, x ≠ y → 3 ≤ ∑ i, if x i ≠ y i then 1 else 0) ∧
      (Finset.univ (α := Fin 5 → Fin 4)).card ≤ C.card * (1 + 5 * (4 - 1)) := by
  sorry

end LefebvreVariations
