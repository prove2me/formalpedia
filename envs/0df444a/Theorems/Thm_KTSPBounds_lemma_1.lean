-- Prove2me | Theorems.Thm_KTSPBounds_lemma_1
-- name    : KTSPBounds.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:38:46.400721+00:00
-- url     : https://prove2.me/theorems/4e61f33a-ad35-4f3a-9bd7-c5ec5ab84c22
-- title:
--   Lemma 1, p.5 — the tour through $n$ points of the unit square
-- statement:
--   There is a universal constant $C > 0$ such that, for every $n \ge 2$ and all points $X_1,\dots,X_n$ in the unit square $[0,1]^2$,
--
--   $$
--   l_{TSP}(X_1,\dots,X_n) \le 2\sqrt n + C.
--   $$
--
--   The bound is deterministic. After rescaling it bounds the tour through $k$ points of a small cell.
--
--   Differences from the source:
--   - encoding: for some universal constant → the existential quantifier stands before n and the points; reason: this is what universal means
--   - encoding: the TSP tour → tourLength x, the optimal closed tour (1) via MetricTSP.tspOpt; reason: the same minimum over orderings; coordinates in [0,1] are written coordinatewise
-- source:
--   Blanchard, Jacquillat, Jaillet, Probabilistic bounds on the k-Traveling Salesman Problem and the Traveling Repairman Problem, arXiv:2211.11063v1, Lemma 1, p.5 (cited from Beardwood et al.)

import Mathlib
import Definitions.Def_KTSPBounds_tourLength

namespace KTSPBounds

/-- Lemma 1, p.5 (cited there from Beardwood et al.), Blanchard, Jacquillat, Jaillet, arXiv:2211.11063v1: there is a universal
constant `C > 0` such that the optimal closed TSP tour through any `n ≥ 2` points of the unit
square `[0, 1]²` has length at most `2√n + C`.

**Formalization Note.** The constant `C` is quantified before `n` and the points. The statement
is deterministic. -/
theorem lemma_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 2 ≤ n → ∀ x : Fin n → Plane,
      (∀ i j, x i j ∈ Set.Icc (0 : ℝ) 1) →
        tourLength x ≤ 2 * Real.sqrt (n : ℝ) + C := by sorry

end KTSPBounds
