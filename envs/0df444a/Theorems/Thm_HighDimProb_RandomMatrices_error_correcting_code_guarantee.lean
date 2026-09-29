-- Prove2me | Theorems.Thm_HighDimProb_RandomMatrices_error_correcting_code_guarantee
-- name    : HighDimProb.RandomMatrices.error_correcting_code_guarantee
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T21:24:20.725267+00:00
-- url     : https://prove2.me/theorems/fadb1218-b577-4398-877b-85cd7d197857
-- title:
--   Theorem 4.3.5 — Guarantees for an error correcting code
-- statement:
--   This is **Theorem 4.3.5**: an application of the packing/covering machinery of §4.2 to
--   coding theory, demonstrating (on a clean discrete statement, independent of the goal
--   theorem's own proof path) how covering/packing numbers of a metric space — here the
--   Hamming cube, rather than a Euclidean ball — control a concrete combinatorial guarantee.
--
--   Assume positive integers $k, n, r$ satisfy
--
--   $$
--   n \;\ge\; k + 2r \log_2\!\left(\frac{en}{2r}\right).
--   $$
--
--   Then there exists an error correcting code (companion definition `IsErrorCorrectingCode`)
--   that encodes $k$-bit strings into $n$-bit strings and can correct $r$ errors.
--
--   **Formalization Note** $e$ is Euler's number, `Real.exp 1`; $\log_2$ is `Real.logb 2`. The
--   hypothesis and conclusion are stated exactly as the book's, with $k, n, r$ required positive
--   per "Assume that positive integers $k, n$ and $r$".
-- source:
--   Vershynin, High-Dimensional Probability (2018), Theorem 4.3.5, p. 88 (PDF p. 96)

import Mathlib
import Definitions.Def_HighDimProb_RandomMatrices_hammingDist
import Definitions.Def_HighDimProb_RandomMatrices_IsErrorCorrectingCode

namespace HighDimProb.RandomMatrices

/-- **Theorem 4.3.5** (Guarantees for an error correcting code), Vershynin, *High-Dimensional
Probability* (2018), p. 88.

Assume that positive integers `k, n, r` are such that `n ≥ k + 2r log₂(en/(2r))`. Then there
exists an error correcting code that encodes `k`-bit strings into `n`-bit strings and can
correct `r` errors. -/
theorem error_correcting_code_guarantee (k n r : ℕ) (hk : 0 < k) (hn : 0 < n) (hr : 0 < r)
    (h : (n : ℝ) ≥ (k : ℝ) + 2 * (r : ℝ) * Real.logb 2 (Real.exp 1 * (n : ℝ) / (2 * (r : ℝ)))) :
    ∃ E : (Fin k → Bool) → (Fin n → Bool), ∃ D : (Fin n → Bool) → (Fin k → Bool),
      IsErrorCorrectingCode (r := r) E D := by sorry

end HighDimProb.RandomMatrices
