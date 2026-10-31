-- Prove2me | Theorems.Thm_MixedManna_lemma_19
-- name    : MixedManna.lemma_19
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:16:49.724735+00:00
-- url     : https://prove2.me/theorems/77425b1f-1ab5-4f77-ba0e-6b68e037608e
-- title:
--   Lemma 19 — Algorithm 1 never reaches the degenerate solution
-- statement:
--   Consider an instance satisfying the standing assumptions and $P>0$. There is $R_0$ such that for every $R\ge R_0$, admissible $\delta$ and $\varepsilon>0$, if every vertex of $\mathcal P$ with $z>0$, $p<P$, $r<R$ is nondegenerate, then Algorithm 1, started from the primary ray, never reaches the degenerate solution $p_j=P$ $(j\in M)$, $r_i=R$ $(i\in N)$, with all other variables, including $z$, equal to zero.
--
--   The degenerate solution solves LCP (14) but is not an equilibrium; this lemma is what separates the LCP's spurious solution from the algorithm's output.
--
--   Differences from the source:
--   - reading: bads: 0 ≥ U_ijk > U_ijk′ (p.14), which allows U_ij1 = 0 → every slope on a bad is strictly negative, D_ijk = |U_ijk| > 0 (StandingAssumptions.bad_slope_neg); reason: the paper's working assumption in its proofs (p.24: 0 < D_ij1 < ⋯; p.43: D_ijk = |U_ijk| > 0 for all (i, j, k)); with D_ij1 = 0, (14d) fails at S₀ and Algorithm 1 cannot start; indifference_j < 1 for bads then holds automatically and is not stated
--   - encoding: a set of agents N and a set of items M → finite types with N nonempty; segments indexed from 0; reason: a market with no agents has no items (unit supply); Lean convention for indices; same instances otherwise
--   - encoding: Algorithm 1 starting from the primary ray reaches a vertex → the vertex is the end w T of some w with IsLemkePath I P R δ ε w T (w₀ = S₀, vertices of 𝒫, pairwise distinct, consecutive segments inside the LCP solution set, z > 0 before the end); reason: under the nondegeneracy hypothesis these are the vertex sequences Algorithm 1 visits (p.6, p.22)
--   - reading: Algorithm 1 run under the assumption that U, W, L have no polynomial relationship (p.22), which guarantees a unique double label through Theorem 11 → hypothesis NondegenerateInRegion: every vertex of 𝒫 with z > 0, p < P, r < R is nondegenerate; reason: the printed condition is undefined and, read as algebraic independence, never holds (Σ_i W_ij = 1); the proofs use only Theorem 11's conclusion (pp.22, 28)
--   - reading: for sufficiently large R (p.22; Theorem 20's proof, p.27) → ∃ R₀, ∀ R ≥ R₀ (R₀ depending on the instance and P only); reason: the explicit list on p.22 cannot hold for zero-slope good segments (P − U_ijk R < 0 fails when U_ijk = 0), so the threshold is existential
--   - generalization: δ_j = 1 + ϵ_j with ϵ_j a uniform random number from (0, 1/m) (p.21) → every δ with 1 < δ_j < 1 + 1/m on goods (IsAdmissibleDelta); reason: every draw lies in the interval, so the statement specializes to the paper's
--   - generalization: last segment of length 1 + ϵ for some small ϵ > 0 in the LCP (p.14, p.23) → every ε > 0 (lcpLength); reason: the proofs use only that the length exceeds 1; specializes to small ε
-- source:
--   Chaudhury, Garg, McGlaughlin, Mehta, Competitive Allocation of a Mixed Manna, arXiv:2008.02753v1, Lemma 19, p.26 (PDF p.28)

import Mathlib
import Definitions.Def_MixedManna_StandingAssumptions
import Definitions.Def_MixedManna_IsAdmissibleDelta
import Definitions.Def_MixedManna_IsNondegenerateVertex
import Definitions.Def_MixedManna_IsLemkePath
import Definitions.Def_MixedManna_degenerateSolution

namespace MixedManna

open Classical

/-- **Lemma 19** (Chaudhury, Garg, McGlaughlin, Mehta, *Competitive Allocation of a Mixed Manna*, arXiv:2008.02753v1, p.26): "Starting from the primary ray, Algorithm 1 never reaches the
solution `p_j = P`, `∀j ∈ M`, and `r_i = R`, `∀i ∈ N`, with all other variables, including `z`,
equal to zero."

**Formalization Note** "Starting from the primary ray, Algorithm 1 reaches a vertex `v`" is
"`v = w T` for a path `IsLemkePath I P R δ ε w T`" (see `IsLemkePath`). The lemma is stated in the
setting of Theorem 14: the standing assumptions, any `P > 0`, every sufficiently large `R` (the
threshold `R₀` is existential, p.22: "for sufficiently large R"), every admissible `δ`, every
last-segment length `1 + ε`, `ε > 0`, and the nondegeneracy of the vertices with `z > 0`,
`p < P`, `r < R` that Theorem 11 provides. -/
theorem lemma_19 {N M : Type*} [Fintype N] [Fintype M] (I : Instance N M)
    (hI : StandingAssumptions I) (P : ℝ) (hP : 0 < P) :
    ∃ R₀ : ℝ, ∀ R ≥ R₀, ∀ δ : M → ℝ, IsAdmissibleDelta I δ → ∀ ε : ℝ, 0 < ε →
      NondegenerateInRegion I P R δ ε →
      ∀ (w : ℕ → LCPVar I) (T : ℕ), IsLemkePath I P R δ ε w T →
      w T ≠ degenerateSolution I P R := by sorry

end MixedManna
