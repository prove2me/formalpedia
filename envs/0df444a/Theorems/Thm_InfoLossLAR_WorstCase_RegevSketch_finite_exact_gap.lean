-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_finite_exact_gap
-- name    : InfoLossLAR.WorstCase.RegevSketch.finite_exact_gap
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T08:53:28.781237+00:00
-- url     : https://prove2.me/theorems/76aeda4b-c9ea-43cc-98ff-f2fc2ea394be
-- title:
--   Exact GapSVP in all dimensions below a fixed cutoff
-- statement:
--   For every fixed natural cutoff $N_0$, there is one uniform quantum polynomial-time family $E$ such that, for every positive $n<N_0$, it solves exact decision GapSVP in dimension $n$ for all nonsingular integer bases and positive rational thresholds. In particular the running time must be polynomial in the full binary instance length, including arbitrarily large matrix entries and thresholds; there is no finite table of instances. A single family handles all dimensions below the fixed cutoff.
-- source:
--   Daniele Micciancio and Panagiotis Voulgaris, A deterministic single exponential time algorithm for most lattice problems based on Voronoi cell computations, https://cseweb.ucsd.edu/~daniele/papers/Voronoi.pdf, Introduction and §2 (especially discussion of basis-bit-size dependence). The finite-cutoff circuit-family formulation and the rational-threshold comparison are explicit consequences adapted to the platform encoding, not a verbatim theorem in the paper.

import Definitions.Def_InfoLossLAR_RegevSketch_DGS

set_option autoImplicit false
open QAlgorithms.Complexity InfoLossLAR.WorstCase

namespace InfoLossLAR.WorstCase.RegevSketch

theorem finite_exact_gap (cutoff : ℕ) :
  ∃ E : Family, IsQPT E ∧ ∀ n : ℕ, 1 ≤ n → n < cutoff → SolvesGapSVP E (famN n) 1 := by sorry

end InfoLossLAR.WorstCase.RegevSketch
