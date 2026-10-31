-- Prove2me | Theorems.Thm_MixedManna_claim_1
-- name    : MixedManna.claim_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:16:02.002017+00:00
-- url     : https://prove2.me/theorems/2487b8a6-c2fe-4807-8583-7ed7d012f95d
-- title:
--   Claim 1 — supplementary prices of final segments vanish when p < P
-- statement:
--   Consider an instance satisfying the standing assumptions, $P>0$, any $R$, admissible $\delta$ and last-segment length $1+\varepsilon$, $\varepsilon>0$. Let $(p,f,r,s,z)$ be a solution of LCP (14) with $p_j<P$ for every $j\in M$, and let $(i,j,k)$ be agent $i$'s final segment for item $j$. Then
--
--   1. if $j\in M^-$, then $s_{ijk}=0$;
--   2. if $j\in M^+$ and $p_j>0$, then $s_{ijk}=0$.
--
--   The claim says a final segment is never forced; it is the basic tool in Lemmas 15–18.
--
--   Differences from the source:
--   - reading: bads: 0 ≥ U_ijk > U_ijk′ (p.14), which allows U_ij1 = 0 → every slope on a bad is strictly negative, D_ijk = |U_ijk| > 0 (StandingAssumptions.bad_slope_neg); reason: the paper's working assumption in its proofs (p.24: 0 < D_ij1 < ⋯; p.43: D_ijk = |U_ijk| > 0 for all (i, j, k)); with D_ij1 = 0, (14d) fails at S₀ and Algorithm 1 cannot start; indifference_j < 1 for bads then holds automatically and is not stated
--   - encoding: a set of agents N and a set of items M → finite types with N nonempty; segments indexed from 0; reason: a market with no agents has no items (unit supply); Lean convention for indices; same instances otherwise
--   - encoding: a solution to LCP (14) → a point of lcpSolutions: the polyhedron 𝒫 of (14a)–(14f) with all variables ≥ 0 and every complementarity product zero; f, s indexed by the segments carrying variables (p.17); reason: the ⊥ convention of p.6 and p.17; same objects
--   - generalization: R chosen large (R > P / min |U_ijk|, p.20) → any real R; reason: the proof does not use R; specializes to the paper's R
--   - generalization: δ_j = 1 + ϵ_j with ϵ_j a uniform random number from (0, 1/m) (p.21) → every δ with 1 < δ_j < 1 + 1/m on goods (IsAdmissibleDelta); reason: every draw lies in the interval, so the statement specializes to the paper's
--   - generalization: last segment of length 1 + ϵ for some small ϵ > 0 in the LCP (p.14, p.23) → every ε > 0 (lcpLength); reason: the proofs use only that the length exceeds 1; specializes to small ε
-- source:
--   Chaudhury, Garg, McGlaughlin, Mehta, Competitive Allocation of a Mixed Manna, arXiv:2008.02753v1, Claim 1, p.23 (PDF p.25)

import Mathlib
import Definitions.Def_MixedManna_StandingAssumptions
import Definitions.Def_MixedManna_IsAdmissibleDelta
import Definitions.Def_MixedManna_lcpSolutions

namespace MixedManna

open Classical

/-- **Claim 1** (Chaudhury, Garg, McGlaughlin, Mehta, *Competitive Allocation of a Mixed Manna*, arXiv:2008.02753v1, p.23): "Let S be any solution to LCP (14) with `p_j < P`, `∀j ∈ M`.
Pick any agent `i ∈ N`, and any item (good or bad) `j ∈ M`, and let `k = |u_ij|` be `i`'s final
segment for item `j`. If `j ∈ M⁻`, then `s_ijk = 0`. If `j ∈ M⁺` and `p_j > 0`, then `s_ijk = 0`."

**Formalization Note** A solution is a point of `lcpSolutions`; the final segment `(i, j, k)` is a
`σ : Seg I` with `IsLastSeg σ` (on a good it exists only for agents with `U_ij1 > 0`). The final
segment has length `1 + ε > 1` in `(14f)`. `R` is arbitrary. -/
theorem claim_1 {N M : Type*} [Fintype N] [Fintype M] (I : Instance N M)
    (hI : StandingAssumptions I) (P R : ℝ) (hP : 0 < P) (δ : M → ℝ)
    (hδ : IsAdmissibleDelta I δ) (ε : ℝ) (hε : 0 < ε) (x : LCPVar I)
    (hx : x ∈ lcpSolutions I P R δ ε) (hp : ∀ j, pv x j < P) (σ : Seg I) (hσ : IsLastSeg σ) :
    (¬ IsGood I (segItem σ) → sv x σ = 0) ∧
      (IsGood I (segItem σ) → 0 < pv x (segItem σ) → sv x σ = 0) := by sorry

end MixedManna
