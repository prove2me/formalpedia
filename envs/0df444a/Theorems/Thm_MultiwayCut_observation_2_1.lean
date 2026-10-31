-- Prove2me | Theorems.Thm_MultiwayCut_observation_2_1
-- name    : MultiwayCut.observation_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:15:20.399609+00:00
-- url     : https://prove2.me/theorems/2fce6e06-1f5b-490c-a8f7-7ad5ba0eadef
-- title:
--   Observation 2.1 — every pair of points of $\Delta_k$ is joined by a path of short $(i,j)$-edges of total length $\frac12\|u-v\|_1$
-- statement:
--   Observation 2.1 says that, without loss of generality, every edge $(\mathbf u,\mathbf v)$ is an $(i,j)$-edge. The content of this reduction is the following subdivision statement.
--
--   Let $\mathbf u,\mathbf v\in\Delta_k$ and $\delta>0$. There are points $\mathbf u=\mathbf y_0,\mathbf y_1,\dots,\mathbf y_m=\mathbf v$ such that for every step $s$ the pair $(\mathbf y_s,\mathbf y_{s+1})$ or the pair $(\mathbf y_{s+1},\mathbf y_s)$ is an $(i_s,j_s)$-edge, for some order $\pi_s$ of the coordinates and some $i_s<j_s$, with parameter $0\le\varepsilon_s\le\delta$, and
--   $$\sum_{s}\varepsilon_s=\tfrac12\,\|\mathbf u-\mathbf v\|_1 .$$
--
--   Replacing an edge by such a path leaves the relaxation's objective unchanged and, by the union bound, can only increase the probability that its endpoints are separated; this is what the reduction from cut density to approximation uses.
--
--   Differences from the source:
--   - reading: "without loss of generality, every edge is an $(i,j)$-edge" → every pair of points of $\Delta_k$ is joined by a path of $(i,j)$-edges (either orientation, steps at most $\delta$) whose parameters sum to $\frac12\|u-v\|_1$; reason: a WLOG has no truth value of its own; this is the claim the reduction on p.4 needs from it
--   - encoding: positions $1,\dots,k$ in the order of the coordinates → a permutation `π` of `Fin k`, positions from $0$; reason: Lean convention
-- source:
--   Buchbinder, Schwartz & Weizman, Simplex Transformations and the Multiway Cut Problem, manuscript of Nov. 1, 2016, Observation 2.1, p.4 (with the explanation after it, p.4, and Figure 1, p.5)

import Mathlib
import Definitions.Def_MultiwayCut_CutDensity

namespace MultiwayCut

/-- **Observation 2.1** (subdivision into `(i, j)`-edges), Buchbinder, Schwartz & Weizman,
*Simplex Transformations and the Multiway Cut Problem*, manuscript of Nov. 1, 2016, p.4:
"Without loss of generality, one can assume that every edge `(u, v) ∈ E` is of the form
appearing in Figure 1" (an `(i, j)`-edge).

Content of the "without loss of generality": any two points `u, v ∈ Δ_k` are joined by a path
`u = y₀, y₁, …, y_m = v` each of whose steps is an `(i, j)`-edge (in one of its two
orientations, for its own order `π_s` of the coordinates and its own `i_s < j_s`) with
parameter `ε_s ≤ δ`, for any prescribed `δ > 0`, and the parameters add up to the relaxation
length `½ ‖u − v‖₁`. Replacing an edge by such a path keeps the relaxation's objective and can
only increase the cut probability (union bound).

**Formalization Note.** The path is `y : Fin (m + 1) → Fin k → ℝ`; step `s : Fin m` joins
`y s` and `y (s + 1)`. -/
theorem observation_2_1 {k : ℕ} (u v : Fin k → ℝ) (hu : u ∈ stdSimplex ℝ (Fin k))
    (hv : v ∈ stdSimplex ℝ (Fin k)) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (m : ℕ) (y : Fin (m + 1) → Fin k → ℝ) (π : Fin m → Equiv.Perm (Fin k))
      (i j : Fin m → Fin k) (ε : Fin m → ℝ),
      y 0 = u ∧ y (Fin.last m) = v ∧
      (∀ s : Fin m, ε s ≤ δ ∧
        (IsIJEdge (π s) (i s) (j s) (ε s) (y s.castSucc) (y s.succ) ∨
          IsIJEdge (π s) (i s) (j s) (ε s) (y s.succ) (y s.castSucc))) ∧
      ∑ s, ε s = 1 / 2 * ∑ ℓ, |u ℓ - v ℓ| := by sorry

end MultiwayCut
