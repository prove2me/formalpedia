-- Prove2me | Theorems.Thm_MixedManna_theorem_20
-- name    : MixedManna.theorem_20
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:17:45.255475+00:00
-- url     : https://prove2.me/theorems/0acca116-982d-48d3-b50f-d7d66b61216b
-- title:
--   Theorem 20 — Algorithm 1 never reaches a secondary ray
-- statement:
--   Consider an instance satisfying the standing assumptions and $P>0$. There is $R_0$ such that for every $R\ge R_0$, admissible $\delta$ and $\varepsilon>0$, if every vertex of $\mathcal P$ with $z>0$, $p<P$, $r<R$ is nondegenerate, then the following holds. Let Algorithm 1, started from the primary ray, reach a vertex $w_T$ with $z(w_T)>0$, and let $d\ne 0$ be such that the half-line $\{w_T+\alpha d:\alpha\ge 0\}$ lies in the solution set of LCP (14). Then this half-line is the primary ray: $w_T=S_0$ (the path has length $T=0$) and $d$ is a positive multiple of the $z$-direction.
--
--   Since the path never revisits a vertex and $\mathcal P$ has finitely many vertices, excluding secondary rays forces the path to end at $z=0$.
--
--   Differences from the source:
--   - reading: bads: 0 ≥ U_ijk > U_ijk′ (p.14), which allows U_ij1 = 0 → every slope on a bad is strictly negative, D_ijk = |U_ijk| > 0 (StandingAssumptions.bad_slope_neg); reason: the paper's working assumption in its proofs (p.24: 0 < D_ij1 < ⋯; p.43: D_ijk = |U_ijk| > 0 for all (i, j, k)); with D_ij1 = 0, (14d) fails at S₀ and Algorithm 1 cannot start; indifference_j < 1 for bads then holds automatically and is not stated
--   - encoding: a set of agents N and a set of items M → finite types with N nonempty; segments indexed from 0; reason: a market with no agents has no items (unit supply); Lean convention for indices; same instances otherwise
--   - encoding: Algorithm 1 starting from the primary ray reaches a vertex → the vertex is the end w T of some w with IsLemkePath I P R δ ε w T (w₀ = S₀, vertices of 𝒫, pairwise distinct, consecutive segments inside the LCP solution set, z > 0 before the end); reason: under the nondegeneracy hypothesis these are the vertex sequences Algorithm 1 visits (p.6, p.22)
--   - reading: Algorithm 1 run under the assumption that U, W, L have no polynomial relationship (p.22), which guarantees a unique double label through Theorem 11 → hypothesis NondegenerateInRegion: every vertex of 𝒫 with z > 0, p < P, r < R is nondegenerate; reason: the printed condition is undefined and, read as algebraic independence, never holds (Σ_i W_ij = 1); the proofs use only Theorem 11's conclusion (pp.22, 28)
--   - reading: for sufficiently large R (p.22; Theorem 20's proof, p.27) → ∃ R₀, ∀ R ≥ R₀ (R₀ depending on the instance and P only); reason: the explicit list on p.22 cannot hold for zero-slope good segments (P − U_ijk R < 0 fails when U_ijk = 0), so the threshold is existential
--   - generalization: δ_j = 1 + ϵ_j with ϵ_j a uniform random number from (0, 1/m) (p.21) → every δ with 1 < δ_j < 1 + 1/m on goods (IsAdmissibleDelta); reason: every draw lies in the interval, so the statement specializes to the paper's
--   - generalization: last segment of length 1 + ϵ for some small ϵ > 0 in the LCP (p.14, p.23) → every ε > 0 (lcpLength); reason: the proofs use only that the length exceeds 1; specializes to small ε
--   - generalization: a ray: an unbounded edge of S incident to a vertex (y*, z*) with z* > 0, {(y*, z*) + α(y′, z′) : α ≥ 0} (p.6, p.22) → every half-line in the LCP solution set from the vertex w T with z(w T) > 0, direction d ≠ 0; reason: every ray is such a half-line, so the statement specializes to rays
--   - encoding: never reaches a secondary ray (one other than the primary ray) → every such half-line is the primary ray: T = 0 and d = c · (0, 1) with c > 0; reason: the primary ray {(0, z) : z ≥ z₀} starts at S₀ = w₀, and the path's vertices are distinct
-- source:
--   Chaudhury, Garg, McGlaughlin, Mehta, Competitive Allocation of a Mixed Manna, arXiv:2008.02753v1, Theorem 20, p.27 (PDF p.29)

import Mathlib
import Definitions.Def_MixedManna_StandingAssumptions
import Definitions.Def_MixedManna_IsAdmissibleDelta
import Definitions.Def_MixedManna_IsNondegenerateVertex
import Definitions.Def_MixedManna_IsLemkePath

namespace MixedManna

open Classical

/-- **Theorem 20** (Chaudhury, Garg, McGlaughlin, Mehta, *Competitive Allocation of a Mixed Manna*, arXiv:2008.02753v1, p.27): "Starting from the primary ray, the Algorithm 1 never reaches a
secondary ray."

A ray is `{(y*, z*) + α (y′, z′) : α ≥ 0} ⊆ S` with direction `(y′, z′) ≠ 0`, incident to a vertex
`(y*, z*)` with `z* > 0` (p.6, p.22); the primary ray is `{(0, z) : z ≥ z₀}`, every other ray is
secondary. Stated: if a path of Algorithm 1 ends at `w T` with `z(w T) > 0` and the half-line from
`w T` in direction `d ≠ 0` lies in the solution set of LCP (14), then this half-line is the primary
ray: `T = 0` (so `w T = S₀`) and `d` is a positive multiple of the `z`-direction.

**Formalization Note** "Starting from the primary ray, Algorithm 1 reaches a vertex `v`" is
"`v = w T` for a path `IsLemkePath I P R δ ε w T`" (see `IsLemkePath`). The lemma is stated in the
setting of Theorem 14: the standing assumptions, any `P > 0`, every sufficiently large `R` (the
threshold `R₀` is existential, p.22: "for sufficiently large R"), every admissible `δ`, every
last-segment length `1 + ε`, `ε > 0`, and the nondegeneracy of the vertices with `z > 0`,
`p < P`, `r < R` that Theorem 11 provides. -/
theorem theorem_20 {N M : Type*} [Fintype N] [Fintype M] (I : Instance N M)
    (hI : StandingAssumptions I) (P : ℝ) (hP : 0 < P) :
    ∃ R₀ : ℝ, ∀ R ≥ R₀, ∀ δ : M → ℝ, IsAdmissibleDelta I δ → ∀ ε : ℝ, 0 < ε →
      NondegenerateInRegion I P R δ ε →
      ∀ (w : ℕ → LCPVar I) (T : ℕ), IsLemkePath I P R δ ε w T →
      0 < zv (w T) → ∀ d : LCPVar I, d ≠ 0 →
        (∀ α : ℝ, 0 ≤ α → w T + α • d ∈ lcpSolutions I P R δ ε) →
          T = 0 ∧ ∃ c : ℝ, 0 < c ∧ d = c • zUnit I := by sorry

end MixedManna
