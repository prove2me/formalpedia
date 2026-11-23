-- Prove2me | Theorems.Thm_Kyprianou_Ch02_cadlagNNRealDiscontinuitiesCountableV1
-- name    : Kyprianou.Ch02.cadlagNNRealDiscontinuitiesCountableV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T19:12:50.546266+00:00
-- url     : https://prove2.me/theorems/4b765896-ec0c-414b-b89e-e57a3549d72d
-- title:
--   Theorem 2.10: countable discontinuities of a real càdlàg path on nonnegative times
-- statement:
--   Right-continuity and existence of finite left limits at every positive time imply countably many discontinuities on the entire nonnegative half-line, by decomposition into compact horizons.
-- source:
--   Kyprianou (2006), Chapter 2, Theorem 2.10, deterministic uniform-limit argument

import Mathlib
open Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem cadlagNNRealDiscontinuitiesCountableV1
    (f : ℝ≥0 → ℝ)
    (hright : ∀ t : ℝ≥0, ContinuousWithinAt f (Set.Ici t) t)
    (hleft : ∀ t : ℝ≥0, 0 < t →
      ∃ l : ℝ, Tendsto f (nhdsWithin t (Set.Iio t)) (nhds l)) :
    Set.Countable {t : ℝ≥0 | ¬ ContinuousAt f t}
    := by sorry
end Kyprianou.Ch02
