-- Prove2me | Theorems.Thm_MultiStageAlloc_proposition_1
-- name    : MultiStageAlloc.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:30:38.655481+00:00
-- url     : https://prove2.me/theorems/858e4381-b4fd-41fe-9b7b-debaeea01146
-- title:
--   Proposition 1 — the recursive sequence of polynomial regularizers
-- statement:
--   Fix $K\ge 1$. The functions $f_k$ solve the backward recursion on $[0,1]$
--   $$
--   f_K(x)=\mathbb I\{x=1\},\qquad f_k(x)=\max_{y\in[0,1-x]}(1-y)f_{k+1}(x+y)\quad(k\in[K-1]),
--   $$
--   take values in $[0,1]$, and are the only solution of this recursion. Moreover:
--
--   1. for $k\in[K-1]$, $f_k(x)=\bigl(1-\tfrac{1-x}{K-k}\bigr)^{K-k}$, a polynomial of degree $K-k$;
--   2. for $k\in[K-1]$, $f_k$ is strictly increasing and continuous on $[0,1]$, and $F_k(x)=\int_0^xf_k$ is differentiable and strictly convex on $[0,1]$;
--   3. for $k\in[K]$ and $x\in[0,1]$, $f_k(x)\le e^{x-1}$, and the first function converges pointwise to $e^{x-1}$ from below as $K\to\infty$: it is nondecreasing in $K\ge 2$ at each $x\in[0,1]$;
--   4. $\min_{y\in[0,1]}\ 1-(1-y)f_1(y)=1-(1-1/K)^K=\Gamma(K)$, and the minimum is attained.
--
--   This is what ties the regularizers to the competitive ratio: Algorithm 1 is built from $f_k$, and the telescoping of Lemma 1 ends at item 4.
--
--   Differences from the source:
--   - reading: "Consider a sequence … satisfying" the recursion → the closed form satisfies it, and any sequence satisfying it equals the closed form on [0,1]; reason: this is existence and uniqueness, which is all the wording can mean; the proof (B.1) is by backward induction
--   - generalization: functions f_k : [0,1] → [0,1] → the uniqueness clause takes any f_k : ℝ → ℝ and assumes nothing about their range; reason: the source class is a subclass; the range [0,1] of the solution is a separate conclusion
--   - reading: "max", "min" → attained (IsGreatest, IsLeast); reason: the page writes max and min, so attainment is claimed
--   - reading: "polynomials with decreasing degrees" → natDegree = K − k; reason: the sentence before Proposition 1 on p.14 says "a polynomial of degree K − k for each stage"
--   - reading: "monotone increasing" → StrictMonoOn on [0,1]; reason: clause (ii) derives strict convexity of F_k from it, which needs strict monotonicity; the stronger reading
--   - reading: "converges point-wise from below" → the limit as K → ∞ at each x ∈ [0,1], with the bound f_k ≤ e^(x−1) for each K, and f_1 nondecreasing in K ≥ 2; reason: the proof (B.1, p.38) gives the bound and the limit, and monotonicity in K is the stronger meaning of "from below"; the formula for f_1 starts at K = 2, since at K = 1 the first function is the indicator
--   - reading: K ∈ ℕ → K ≥ 1; reason: the paper’s K > 0 (p.4); at K = 0 there are no stages and Γ(0) would be a division by zero
-- source:
--   Feng & Niazadeh, Batching and Optimal Multi-stage Bipartite Allocations, arXiv:2211.16581v1, Proposition 1, pp.14–15

import Mathlib
import Definitions.Def_MultiStageAlloc_Regularizers

open Filter Topology

namespace MultiStageAlloc

/-- **Proposition 1 (Sequence of Polynomial Regularizers).** Feng & Niazadeh, *Batching and Optimal
Multi-stage Bipartite Allocations*, arXiv:2211.16581v1, pp.14–15.

The conjuncts, in order: `regPoly` satisfies the backward recursion (base case, recursive case, with
`max` read as attained, values in `[0, 1]`); any sequence satisfying the recursion equals `regPoly` on
`[0, 1]`; (i) `f_k` is the printed closed form and a polynomial of degree `K - k`; (ii) `f_k` is
strictly increasing and continuous on `[0, 1]`, and `F_k` differentiable and strictly convex there;
(iii) `f_k(x) ≤ e^(x-1)` for all `k ≤ K`, `f_1^(K)(x) → e^(x-1)` as `K → ∞`, and `f_1^(K)(x)` is
nondecreasing in `K ≥ 2`; (iv)
`min_{y ∈ [0,1]} 1 - (1 - y) f_1(y) = Γ(K)`.

**Formalization Note.** "Converges point-wise from below" is the limit, the bound in (iii), and
monotonicity in `K`, the strongest reading; the formula for `f_1` starts at `K = 2`. -/
theorem proposition_1 (K : ℕ) (hK : 1 ≤ K) :
    (∀ x ∈ Set.Icc (0 : ℝ) 1, regPoly K K x = if x = 1 then 1 else 0) ∧
    (∀ k, 1 ≤ k → k < K → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      IsGreatest ((fun y => (1 - y) * regPoly K (k + 1) (x + y)) '' Set.Icc 0 (1 - x))
        (regPoly K k x)) ∧
    (∀ k, 1 ≤ k → k ≤ K → ∀ x ∈ Set.Icc (0 : ℝ) 1, regPoly K k x ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ f : ℕ → ℝ → ℝ,
      (∀ x ∈ Set.Icc (0 : ℝ) 1, f K x = if x = 1 then 1 else 0) →
      (∀ k, 1 ≤ k → k < K → ∀ x ∈ Set.Icc (0 : ℝ) 1,
        IsGreatest ((fun y => (1 - y) * f (k + 1) (x + y)) '' Set.Icc 0 (1 - x)) (f k x)) →
      ∀ k, 1 ≤ k → k ≤ K → ∀ x ∈ Set.Icc (0 : ℝ) 1, f k x = regPoly K k x) ∧
    (∀ k, 1 ≤ k → k < K →
      (∀ x, regPoly K k x = (1 - (1 - x) / ((K - k : ℕ) : ℝ)) ^ (K - k)) ∧
      ∃ p : Polynomial ℝ, p.natDegree = K - k ∧ ∀ x, p.eval x = regPoly K k x) ∧
    (∀ k, 1 ≤ k → k < K →
      StrictMonoOn (regPoly K k) (Set.Icc 0 1) ∧ ContinuousOn (regPoly K k) (Set.Icc 0 1) ∧
      DifferentiableOn ℝ (regF K k) (Set.Icc 0 1) ∧
      StrictConvexOn ℝ (Set.Icc 0 1) (regF K k)) ∧
    (∀ k, 1 ≤ k → k ≤ K → ∀ x ∈ Set.Icc (0 : ℝ) 1, regPoly K k x ≤ Real.exp (x - 1)) ∧
    (∀ x ∈ Set.Icc (0 : ℝ) 1,
      Tendsto (fun K' : ℕ => regPoly K' 1 x) atTop (𝓝 (Real.exp (x - 1)))) ∧
    (∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ K' : ℕ, 2 ≤ K' → regPoly K' 1 x ≤ regPoly (K' + 1) 1 x) ∧
    IsLeast ((fun y => 1 - (1 - y) * regPoly K 1 y) '' Set.Icc 0 1) (gammaK K) := by sorry

end MultiStageAlloc
