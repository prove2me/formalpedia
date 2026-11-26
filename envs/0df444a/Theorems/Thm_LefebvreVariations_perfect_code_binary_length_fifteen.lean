-- Prove2me | Theorems.Thm_LefebvreVariations_perfect_code_binary_length_fifteen
-- name    : LefebvreVariations.perfect_code_binary_length_fifteen
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T01:03:49.205719+00:00
-- url     : https://prove2.me/theorems/88cb8d95-5c88-5675-ac19-6783cadb1e57
-- title:
--   Lefebvre's variations: a perfect binary one-error-correcting code of length fifteen
-- statement:
--   There is a set $C\subseteq\{0,\dots,1\}^{15}$ of words of length $15$ over an alphabet of $2$ letters such that any two distinct words differ in at least $3$ positions, and the Hamming balls of radius $1$ around the words of $C$ cover the whole space:
--   $$
--   2^{15}\le |C|\,\bigl(1+15(2-1)\bigr).
--   $$
--   Since the balls are disjoint, this means $C$ is a perfect $1$-error-correcting code, $|C|=2^{11}$ (the binary Hamming code of length 15 and dimension 11).
--
--   **Formalization Note** This is the case $n=15$, $q=2$ of the existence half of the platform's `perfect_1_error_correcting_code`: words are functions `Fin 15 → Fin 2`, the distance is `∑ i, if x i ≠ y i then 1 else 0`, and the covering inequality is `(Finset.univ).card ≤ C.card * (1 + 15 * (2 - 1))`.
--
--   **Why this is a variation.** A variation on the platform's open `perfect_1_error_correcting_code`: the existence half at the single size n = 15, q = 2, where it is a classical Hamming code. The general classification (for example q = 6) remains open in the parent.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   The binary Hamming code of length 15 (2048 words, minimum distance 3). Parent: classification of perfect 1-error-correcting codes, on the platform as `perfect_1_error_correcting_code` (open). Hamming, Error detecting and error correcting codes, Bell System Tech. J. 29 (1950) 147-160 (cited from memory). The existence statement itself was verified here by explicit construction (parity-check matrix) and computer check of minimum distance and size.

import Mathlib

namespace LefebvreVariations

/-- A perfect 1-error-correcting code of length `15` over an alphabet of size `2` exists (the binary Hamming code of length 15 and dimension 11). Source: R. W. Hamming, Error detecting and error correcting codes, Bell System Tech. J. 29 (1950) 147-160 (cited from memory). -/
theorem perfect_code_binary_length_fifteen :
    ∃ (C : Finset (Fin 15 → Fin 2)),
      (∀ x ∈ C, ∀ y ∈ C, x ≠ y → 3 ≤ ∑ i, if x i ≠ y i then 1 else 0) ∧
      (Finset.univ (α := Fin 15 → Fin 2)).card ≤ C.card * (1 + 15 * (2 - 1)) := by
  sorry

end LefebvreVariations
