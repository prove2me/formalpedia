-- Prove2me | Theorems.Thm_MixedManna_lemma_7
-- name    : MixedManna.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:14:37.752117+00:00
-- url     : https://prove2.me/theorems/c99af447-1bc3-420f-be75-2b66a5aeaaa0
-- title:
--   Lemma 7 — equilibria satisfy (11a)–(11c); positive solutions of (11a)–(11c) clear the market (corrected: first half for equilibria with the signs of p.14)
-- statement:
--   Consider an instance satisfying the standing assumptions.
--
--   1. If $p^*$ is an equilibrium price vector (with some allocation $x^*$) with $p^*_j\ge 0$ on goods and $p^*_j\le 0$ on bads, there are spendings $f$ such that $(p,f)$ satisfies (11a), (11b), (11c), where $p=|p^*|$ componentwise.
--   2. If $p$ and $f$ satisfy (11a), (11b), (11c) and $p_j>0$ for every $j$, then the market clears: with $x_{ij}=\sum_k f_{ijk}/p_j$,
--   $$
--   \sum_{i\in N}x_{ij}=\sum_{i\in N}W_{ij}\qquad\forall j\in M .
--   $$
--
--   The lemma reduces market clearing to linear inequalities, the first step of the LCP formulation.
--
--   Differences from the source:
--   - reading: bads: 0 ≥ U_ijk > U_ijk′ (p.14), which allows U_ij1 = 0 → every slope on a bad is strictly negative, D_ijk = |U_ijk| > 0 (StandingAssumptions.bad_slope_neg); reason: the paper's working assumption in its proofs (p.24: 0 < D_ij1 < ⋯; p.43: D_ijk = |U_ijk| > 0 for all (i, j, k)); with D_ij1 = 0, (14d) fails at S₀ and Algorithm 1 cannot start; indifference_j < 1 for bads then holds automatically and is not stated
--   - encoding: a set of agents N and a set of items M → finite types with N nonempty; segments indexed from 0; reason: a market with no agents has no items (unit supply); Lean convention for indices; same instances otherwise
--   - encoding: p* is an equilibrium price vector → (p*, x*) is a competitive equilibrium for some x* (IsCompetitiveEquilibrium); reason: same notion
--   - correction: p* is an equilibrium price vector → (p*, x*) is a competitive equilibrium with p*_j ≥ 0 on goods and p*_j ≤ 0 on bads; reason: false as printed under the budget equality of p.5, which does not imply the signs p.14 asserts of every equilibrium ((−p, x) has the same budget sets as (p, x)): for u_A = y1 − 2y2 − y3, u_B = −2y1 + y2 − y3, W_A = (1/2, 3/4, 1/2), W_B = (1/2, 1/4, 1/2), which meets every standing assumption, p* = (1, −2, −1), x_A = (1, 3/4, 1), x_B = (0, 1/4, 0) is a competitive equilibrium, and (11a) for B with (11b), (11c) at p = |p*| force 3/2 ≤ f_B3 ≤ 1; the paper's proof sets f = x*p with these signs
--   - encoding: (p, f) satisfies (11a), (11b), (11c); the market clears → SatisfiesSystem11 (with p, f ≥ 0, f indexed by the segments carrying variables); Σ_i Σ_k f_ijk / p_j = Σ_i W_ij for every j; reason: the LCP's variables are nonnegative; x_ij = Σ_k f_ijk / p_j as in the proof (p.45)
-- source:
--   Chaudhury, Garg, McGlaughlin, Mehta, Competitive Allocation of a Mixed Manna, arXiv:2008.02753v1, Lemma 7, p.19 (PDF p.21), proof p.44–45

import Mathlib
import Definitions.Def_MixedManna_StandingAssumptions
import Definitions.Def_MixedManna_IsCompetitiveEquilibrium
import Definitions.Def_MixedManna_SatisfiesSystem11

namespace MixedManna

open Classical

/-- **Lemma 7** (Chaudhury, Garg, McGlaughlin, Mehta, *Competitive Allocation of a Mixed Manna*, arXiv:2008.02753v1, p.19): "If `p*` is an equilibrium price vector, then `∃ f` such that
`(p, f)` satisfies (11a), (11b), and (11c), where `p = |p*|`. Further, if `p` and `f` satisfy
(11a), (11b), (11c) and `p > 0`, then the market clears."

Stated (corrected): the first half is for equilibria with `p*_j ≥ 0` on goods and `p*_j ≤ 0` on
bads, the signs p.14 asserts of every equilibrium.

**Formalization Note** "`p*` is an equilibrium price vector" is "`(p*, x*)` is a competitive
equilibrium for some allocation `x*`, with the signs of p.14". The signs are hypotheses because the
budget equality of p.5 does not imply them (`(−p, x)` has the same budget sets as `(p, x)`), and the
first half is false without them: take `u_A = y₁ − 2y₂ − y₃`, `u_B = −2y₁ + y₂ − y₃`,
`W_A = (1/2, 3/4, 1/2)`, `W_B = (1/2, 1/4, 1/2)`; then `p* = (1, −2, −1)`, `x_A = (1, 3/4, 1)`,
`x_B = (0, 1/4, 0)` is a competitive equilibrium in which good 2 has a negative price, and (11b),
(11c), (11a) for `B` force `3/2 ≤ f_B3 ≤ 1`. "The market clears" is `Σ_i x_ij = Σ_i W_ij` for every
item `j`, with `x_ij = Σ_k f_ijk / p_j` (proof, p.45), the sum over the segments of `(i, j)` that
carry variables. The instance satisfies the standing assumptions of §4 (strong connectivity
included, p.19). -/
theorem lemma_7 {N M : Type*} [Fintype N] [Fintype M] (I : Instance N M)
    (hI : StandingAssumptions I) :
    (∀ (pstar : M → ℝ) (xstar : N → M → ℝ), IsCompetitiveEquilibrium I pstar xstar →
      (∀ j, IsGood I j → 0 ≤ pstar j) → (∀ j, ¬ IsGood I j → pstar j ≤ 0) →
      ∃ f : Seg I → ℝ, SatisfiesSystem11 I (fun j => |pstar j|) f) ∧
    (∀ (p : M → ℝ) (f : Seg I → ℝ), SatisfiesSystem11 I p f → (∀ j, 0 < p j) →
      ∀ j, ∑ i, (∑ σ : Seg I, if segAgent σ = i ∧ segItem σ = j then f σ else 0) / p j =
        ∑ i, I.W i j) := by sorry

end MixedManna
