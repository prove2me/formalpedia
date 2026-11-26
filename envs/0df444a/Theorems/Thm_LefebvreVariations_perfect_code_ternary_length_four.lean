-- Prove2me | Theorems.Thm_LefebvreVariations_perfect_code_ternary_length_four
-- name    : LefebvreVariations.perfect_code_ternary_length_four
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T01:03:20.18315+00:00
-- url     : https://prove2.me/theorems/ad9fa5d9-1d50-47e7-9f77-a467cc9ef19e
-- title:
--   Lefebvre's variations: a perfect ternary one-error-correcting code of length four
-- statement:
--   There is a set $C\subseteq\{0,\dots,2\}^{4}$ of words of length $4$ over an alphabet of $3$ letters such that any two distinct words differ in at least $3$ positions, and the Hamming balls of radius $1$ around the words of $C$ cover the whole space:
--   $$
--   3^{4}\le |C|\,\bigl(1+4(3-1)\bigr).
--   $$
--   Since the balls are disjoint, this means $C$ is a perfect $1$-error-correcting code, $|C|=3^{2}$ (the tetracode, the ternary Hamming code of length 4).
--
--   **Formalization Note** This is the case $n=4$, $q=3$ of the existence half of the platform's `perfect_1_error_correcting_code`: words are functions `Fin 4 → Fin 3`, the distance is `∑ i, if x i ≠ y i then 1 else 0`, and the covering inequality is `(Finset.univ).card ≤ C.card * (1 + 4 * (3 - 1))`.
--
--   **Why this is a variation.** A variation on the platform's open `perfect_1_error_correcting_code`: the existence half at the single size n = 4, q = 3, where it is a classical Hamming code. The general classification (for example q = 6) remains open in the parent.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   The tetracode, the ternary Hamming code of length 4 (9 words, minimum distance 3). Parent: classification of perfect 1-error-correcting codes, on the platform as `perfect_1_error_correcting_code` (open). Hamming, Error detecting and error correcting codes, Bell System Tech. J. 29 (1950) 147-160 (cited from memory). The existence statement itself was verified here by explicit construction (parity-check matrix) and computer check of minimum distance and size.

import Mathlib

namespace LefebvreVariations

/-- A perfect 1-error-correcting code of length `4` over an alphabet of size `3` exists (the tetracode, the ternary Hamming code of length 4). Source: R. W. Hamming, Error detecting and error correcting codes, Bell System Tech. J. 29 (1950) 147-160; the tetracode: MacWilliams and Sloane, The Theory of Error-Correcting Codes, Ch. 1 (cited from memory). -/
theorem perfect_code_ternary_length_four :
    ∃ (C : Finset (Fin 4 → Fin 3)),
      (∀ x ∈ C, ∀ y ∈ C, x ≠ y → 3 ≤ ∑ i, if x i ≠ y i then 1 else 0) ∧
      (Finset.univ (α := Fin 4 → Fin 3)).card ≤ C.card * (1 + 4 * (3 - 1)) := by
  sorry

end LefebvreVariations
