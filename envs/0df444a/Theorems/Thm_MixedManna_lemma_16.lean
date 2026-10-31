-- Prove2me | Theorems.Thm_MixedManna_lemma_16
-- name    : MixedManna.lemma_16
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:17:30.572832+00:00
-- url     : https://prove2.me/theorems/fc1c1fb3-fffb-4168-8729-821007794001
-- title:
--   Lemma 16 — reaching p_j = P on a good forces p = P, r = R, z = 0 (read with "=")
-- statement:
--   Consider an instance satisfying the standing assumptions and $P>0$. There is $R_0$ such that for every $R\ge R_0$, admissible $\delta$ and $\varepsilon>0$, if every vertex of $\mathcal P$ with $z>0$, $p<P$, $r<R$ is nondegenerate, then: whenever Algorithm 1, started from the primary ray, reaches a vertex where $p_j=P$ for some good $j\in M^+$, at that vertex
--
--   $$
--   p_{j'}=P\ \ \forall j'\in M,\qquad r_i=R\ \ \forall i\in N,\qquad z=0 .
--   $$
--
--   Together with Lemma 19 this excludes the path ever setting a good's price to $P$ (relative price zero).
--
--   Differences from the source:
--   - reading: bads: 0 ≥ U_ijk > U_ijk′ (p.14), which allows U_ij1 = 0 → every slope on a bad is strictly negative, D_ijk = |U_ijk| > 0 (StandingAssumptions.bad_slope_neg); reason: the paper's working assumption in its proofs (p.24: 0 < D_ij1 < ⋯; p.43: D_ijk = |U_ijk| > 0 for all (i, j, k)); with D_ij1 = 0, (14d) fails at S₀ and Algorithm 1 cannot start; indifference_j < 1 for bads then holds automatically and is not stated
--   - encoding: a set of agents N and a set of items M → finite types with N nonempty; segments indexed from 0; reason: a market with no agents has no items (unit supply); Lean convention for indices; same instances otherwise
--   - encoding: Algorithm 1 starting from the primary ray reaches a vertex → the vertex is the end w T of some w with IsLemkePath I P R δ ε w T (w₀ = S₀, vertices of 𝒫, pairwise distinct, consecutive segments inside the LCP solution set, z > 0 before the end); reason: under the nondegeneracy hypothesis these are the vertex sequences Algorithm 1 visits (p.6, p.22)
--   - reading: Algorithm 1 run under the assumption that U, W, L have no polynomial relationship (p.22), which guarantees a unique double label through Theorem 11 → hypothesis NondegenerateInRegion: every vertex of 𝒫 with z > 0, p < P, r < R is nondegenerate; reason: the printed condition is undefined and, read as algebraic independence, never holds (Σ_i W_ij = 1); the proofs use only Theorem 11's conclusion (pp.22, 28)
--   - reading: for sufficiently large R (p.22; Theorem 20's proof, p.27) → ∃ R₀, ∀ R ≥ R₀ (R₀ depending on the instance and P only); reason: the explicit list on p.22 cannot hold for zero-slope good segments (P − U_ijk R < 0 fails when U_ijk = 0), so the threshold is existential
--   - generalization: δ_j = 1 + ϵ_j with ϵ_j a uniform random number from (0, 1/m) (p.21) → every δ with 1 < δ_j < 1 + 1/m on goods (IsAdmissibleDelta); reason: every draw lies in the interval, so the statement specializes to the paper's
--   - generalization: last segment of length 1 + ϵ for some small ϵ > 0 in the LCP (p.14, p.23) → every ε > 0 (lcpLength); reason: the proofs use only that the length exceeds 1; specializes to small ε
--   - reading: then p_j′ < P for all other items j′ ∈ M, r_i = R, for all i ∈ N, and z = 0 → p_j′ = P for all items j′ ∈ M, r_i = R for all i, z = 0; reason: the statement contradicts its own proof, which assumes p_j′ < P for some item for contradiction and concludes p_j = P at T, M1 = M, N1 = N, r_i = R (p.25); Lemma 18's proof cites the lemma as 'all prices are set to zero, i.e., p_j = P, ∀j ∈ M' (p.26)
-- source:
--   Chaudhury, Garg, McGlaughlin, Mehta, Competitive Allocation of a Mixed Manna, arXiv:2008.02753v1, Lemma 16, p.24 (PDF p.26), with its proof, p.25

import Mathlib
import Definitions.Def_MixedManna_StandingAssumptions
import Definitions.Def_MixedManna_IsAdmissibleDelta
import Definitions.Def_MixedManna_IsNondegenerateVertex
import Definitions.Def_MixedManna_IsLemkePath

namespace MixedManna

open Classical

/-- **Lemma 16** (Chaudhury, Garg, McGlaughlin, Mehta, *Competitive Allocation of a Mixed Manna*, arXiv:2008.02753v1, p.24), read with "=": "Starting from the primary ray, if Algorithm 1
reaches a vertex where `p_j = P` for some good `j ∈ M⁺`, then `p_j′ < P` for all other items
`j′ ∈ M`, `r_i = R`, for all `i ∈ N`, and `z = 0`."

Stated: if a path of Algorithm 1 from the primary ray ends at a vertex with `p_j = P` for some good
`j`, then at that vertex `p_j′ = P` for every item `j′ ∈ M`, `r_i = R` for every agent, and `z = 0`.

**Formalization Note** "Starting from the primary ray, Algorithm 1 reaches a vertex `v`" is
"`v = w T` for a path `IsLemkePath I P R δ ε w T`" (see `IsLemkePath`). The lemma is stated in the
setting of Theorem 14: the standing assumptions, any `P > 0`, every sufficiently large `R` (the
threshold `R₀` is existential, p.22: "for sufficiently large R"), every admissible `δ`, every
last-segment length `1 + ε`, `ε > 0`, and the nondegeneracy of the vertices with `z > 0`,
`p < P`, `r < R` that Theorem 11 provides.
The conclusion "`p_j′ < P` for all other items" is read as "`p_j′ = P` for all items": the proof
derives "`p_j = P` at T. M1 = M, and so N1 = N. By Claim 2, `r_i = R`, `∀i ∈ N`, at T" (p.25)
after assuming "`p_j′ < P` for some item" for contradiction, and Lemma 18's proof cites the lemma as
"otherwise all prices are set to zero, i.e., `p_j = P`, `∀j ∈ M`" (p.26). -/
theorem lemma_16 {N M : Type*} [Fintype N] [Fintype M] (I : Instance N M)
    (hI : StandingAssumptions I) (P : ℝ) (hP : 0 < P) :
    ∃ R₀ : ℝ, ∀ R ≥ R₀, ∀ δ : M → ℝ, IsAdmissibleDelta I δ → ∀ ε : ℝ, 0 < ε →
      NondegenerateInRegion I P R δ ε →
      ∀ (w : ℕ → LCPVar I) (T : ℕ), IsLemkePath I P R δ ε w T →
      (∃ j, IsGood I j ∧ pv (w T) j = P) →
        (∀ j, pv (w T) j = P) ∧ (∀ i, rv (w T) i = R) ∧ zv (w T) = 0 := by sorry

end MixedManna
