-- Prove2me | Theorems.Thm_MixedManna_lemma_15
-- name    : MixedManna.lemma_15
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:16:13.82593+00:00
-- url     : https://prove2.me/theorems/f4c04f98-b44d-44f4-8010-95c5b0739b83
-- title:
--   Lemma 15 — p ≤ P at every LCP (14) solution (corrected: r ≤ R only when some bad has p_j < P)
-- statement:
--   Consider an instance satisfying the standing assumptions, $P>0$, any $R$, admissible $\delta$ and $\varepsilon>0$. At every solution of LCP (14):
--
--   1. $p_j\le P$ for every $j\in M$;
--   2. if $p_j<P$ for some bad $j\in M^-$, then $r_i\le R$ for every $i\in N$;
--   3. if $r_i=R$ for some $i\in N$, then $p_j=P$ for every bad $j\in M^-$.
--
--   The bounds confine the path of Algorithm 1 to the box $p\le P$; clause 3 reduces reaching $r_i=R$ to reaching $p_j=P$ on all bads.
--
--   Differences from the source:
--   - reading: bads: 0 ≥ U_ijk > U_ijk′ (p.14), which allows U_ij1 = 0 → every slope on a bad is strictly negative, D_ijk = |U_ijk| > 0 (StandingAssumptions.bad_slope_neg); reason: the paper's working assumption in its proofs (p.24: 0 < D_ij1 < ⋯; p.43: D_ijk = |U_ijk| > 0 for all (i, j, k)); with D_ij1 = 0, (14d) fails at S₀ and Algorithm 1 cannot start; indifference_j < 1 for bads then holds automatically and is not stated
--   - encoding: a set of agents N and a set of items M → finite types with N nonempty; segments indexed from 0; reason: a market with no agents has no items (unit supply); Lean convention for indices; same instances otherwise
--   - correction: r_i ≤ R, ∀i ∈ N, at any solution to LCP (14) → r_i ≤ R for all i at every solution with p_j < P for some bad j; reason: false as printed: p = P, f = 0, z = 0, r_i = |R| + 1, s_ijk = D_ijk (r_i − R) on bad segments and 0 on good segments solves LCP (14) for every instance satisfying the standing assumptions and every P > 0, R, δ, ε (checked in Lean on Example 6, p.18); the paper uses the clause only where some bad has p_j < P
--   - encoding: a solution to LCP (14) → a point of lcpSolutions: the polyhedron 𝒫 of (14a)–(14f) with all variables ≥ 0 and every complementarity product zero; f, s indexed by the segments carrying variables (p.17); reason: the ⊥ convention of p.6 and p.17; same objects
--   - generalization: R chosen large (R > P / min |U_ijk|, p.20) → any real R; reason: the proof does not use R; specializes to the paper's R
--   - generalization: δ_j = 1 + ϵ_j with ϵ_j a uniform random number from (0, 1/m) (p.21) → every δ with 1 < δ_j < 1 + 1/m on goods (IsAdmissibleDelta); reason: every draw lies in the interval, so the statement specializes to the paper's
--   - generalization: last segment of length 1 + ϵ for some small ϵ > 0 in the LCP (p.14, p.23) → every ε > 0 (lcpLength); reason: the proofs use only that the length exceeds 1; specializes to small ε
-- source:
--   Chaudhury, Garg, McGlaughlin, Mehta, Competitive Allocation of a Mixed Manna, arXiv:2008.02753v1, Lemma 15, p.24 (PDF p.26)

import Mathlib
import Definitions.Def_MixedManna_StandingAssumptions
import Definitions.Def_MixedManna_IsAdmissibleDelta
import Definitions.Def_MixedManna_lcpSolutions

namespace MixedManna

open Classical

/-- **Lemma 15** (Chaudhury, Garg, McGlaughlin, Mehta, *Competitive Allocation of a Mixed Manna*, arXiv:2008.02753v1, p.24), corrected: "At any solution to LCP (14), `p_j ≤ P`, `∀j ∈ M` and
`r_i ≤ R`, `∀i ∈ N`. Further, if `r_i = R` for some `i ∈ N`, then `p_j = P`, `∀j ∈ M⁻`."

Stated: at every solution of LCP (14), (1) `p_j ≤ P` for all `j`; (2) if `p_j < P` for some bad
`j`, then `r_i ≤ R` for all `i`; (3) if `r_i = R` for some `i`, then `p_j = P` for every bad `j`.

**Formalization Note** The printed clause "`r_i ≤ R`, `∀i ∈ N`" is false at solutions with
`p_j = P` on every bad: `p = P`, `f = 0`, `z = 0`, `r_i = R + 1`, `s_ijk = D_ijk` on bad segments,
`s_ijk = 0` on good segments solves LCP (14) for every instance and every `P`, `R`, `δ`, `ε`. Clause
(2) is the printed clause restricted to the solutions where some bad has `p_j < P`, which is where
the paper uses it. `R` is arbitrary. -/
theorem lemma_15 {N M : Type*} [Fintype N] [Fintype M] (I : Instance N M)
    (hI : StandingAssumptions I) (P R : ℝ) (hP : 0 < P) (δ : M → ℝ)
    (hδ : IsAdmissibleDelta I δ) (ε : ℝ) (hε : 0 < ε) (x : LCPVar I)
    (hx : x ∈ lcpSolutions I P R δ ε) :
    (∀ j, pv x j ≤ P) ∧ ((∃ j, ¬ IsGood I j ∧ pv x j < P) → ∀ i, rv x i ≤ R) ∧
      (∀ i, rv x i = R → ∀ j, ¬ IsGood I j → pv x j = P) := by sorry

end MixedManna
