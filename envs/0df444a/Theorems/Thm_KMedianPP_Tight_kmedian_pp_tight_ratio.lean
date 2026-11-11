-- Prove2me | Theorems.Thm_KMedianPP_Tight_kmedian_pp_tight_ratio
-- name    : KMedianPP.Tight.kmedian_pp_tight_ratio
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:02:48.519493+00:00
-- url     : https://prove2.me/theorems/07c9b5e4-b7fa-4d2c-a9ff-8971480422f2
-- title:
--   The approximation ratio of k-median++ with $k+\Delta$ centers is exactly $2B_{k,\Delta}$ in every metric (Theorems 4.5 at $\ell=1$ and 4.8)
-- statement:
--   For all integers $k\ge1$ and $\Delta\ge0$, D-sampling (k-median++, $\ell=1$) with $k+\Delta$ centers satisfies:
--   1. on every metric k-median instance (any metric space $(M,d)$, any nonempty finite multiset $X\subseteq M$),
--   $$\mathbb E[\mathrm{cost}(C_{\mathrm{final}})]\le2B_{k,\Delta}\,\mathrm{OPT},$$
--   where $\mathrm{OPT}$ is the optimal cost with $k$ centers in $M$;
--   2. there is an infinite sequence of metric k-median instances with strictly increasing numbers of input points and $\mathrm{OPT}>0$ on which $\mathbb E[\mathrm{cost}(C_{\mathrm{final}})]/\mathrm{OPT}\to2B_{k,\Delta}$.
--
--   Here $B_{k,0}=1+H_{k-1}$ and, for $\Delta>0$, $B_{k,\Delta}=1+R_{k-1,k+\Delta-1}/\Delta$ with the equal-mass process at $\Gamma=\Delta$. So $2B_{k,\Delta}$ is the exact approximation ratio.
--
--   Differences from the source:
--   - reading: §1.1 / p. 17: "For metric k-median, Theorem 4.5 gives the bound 2B_{k,Δ}, which we show is tight for every k and Δ by a matching lower bound in Theorem 4.8" → the conjunction of (i) Theorem 4.5 at ℓ = 1 with α₁ = 2 (Lemma 3.2), stated for D-sampling against OPT, and (ii) Theorem 4.8; reason: the paper's headline exact ratio, both directions
--   - encoding: a finite (multi)set X ⊆ M of input points → `X : Fin n → M` (input point i is `X i`; repeated points allowed); reason: a finite multiset is an indexed family; same instances
--   - encoding: the first center is sampled uniformly from X (X implicitly nonempty) → hypothesis `0 < n`; reason: excludes only the empty input, on which the algorithm is undefined
--   - encoding: OPT = the minimum cost over k-point solutions in M → `opt X 1 k` = infimum of cost(X, C) over C : Finset M with 1 ≤ |C| ≤ k; reason: k points possibly coinciding = a nonempty set of at most k points; the infimum equals the minimum when attained, and the set is nonempty and bounded below by 0
--   - encoding: E[cost(C_final)] over the algorithm's random choices → `expectedCost X ℓ k Δ`: (1/n) Σ_i of the exact recursion `expFinalCostFrom` over the k + Δ − 1 remaining D^ℓ-samples from {x_i}; reason: the exact finite expectation of the same Markov chain
--   - encoding: footnote 4: if cost(C) = 0 the algorithm terminates → the expectation recursions return the current value when `totalCost = 0`; reason: same process; the next-sample law is undefined there
--   - encoding: clause (i) for every metric space → every `M : Type u` (u a universe parameter of the theorem); reason: universe bookkeeping; u is arbitrary
--   - encoding: an infinite sequence of metric k-median instances → types `Ms m` with `MetricSpace (Ms m)` instances and inputs `X m : Fin (N m) → Ms m`, m ∈ ℕ; reason: each instance is a metric space with a finite multiset input
--   - encoding: "with an increasing number of input points" → `StrictMono N`; reason: strictly increasing sizes, as in the proof (n → ∞)
--   - reading: "the approximation ratio of D-sampling with k + Δ centers approaches 2B_{k,Δ}" → `0 < opt (X m) 1 k` for every m and `Tendsto (fun m => expectedCost (X m) 1 k Δ / opt (X m) 1 k) atTop (𝓝 (2 * B k Δ))`; reason: on one instance the ratio is E[cost(C_final)]/OPT, which needs OPT > 0; the proof's instances have OPT > 0
--   - encoding: metric spaces of any size → the instances live in `Type` (universe 0); reason: an existential: instances in Type 0 are instances
-- source:
--   Kaplan, Naori, Tight Bounds for k-Median++ and Improved Bounds for k-Means++, STOC 2027 submission (manuscript sha256 f017529e…), §1.1 p. 2 (PDF 4); p. 16 (PDF 18), Theorem 4.5 and B_{k,Δ}; p. 11 (PDF 13), α₁ = 2; p. 17 (PDF 19); p. 24 (PDF 26), Theorem 4.8

import Mathlib
import Definitions.Def_KMedianPP_Tight_Sampling
import Definitions.Def_KMedianPP_Tight_EqualMass

set_option autoImplicit false

universe u

namespace KMedianPP.Tight

/-- The exact approximation ratio of k-median++ (Theorem 4.5 at `ℓ = 1` with `α₁ = 2`, together
with Theorem 4.8; §1.1 p. 2 and p. 17): for all integers `k ≥ 1` and `Δ ≥ 0`, D-sampling with
`k + Δ` centers (i) satisfies `E[cost(C_final)] ≤ 2 B_{k,Δ} OPT` on every metric k-median
instance, and (ii) has an infinite sequence of metric instances with strictly increasing numbers
of input points and `OPT > 0` on which `E[cost(C_final)] / OPT → 2 B_{k,Δ}`. -/
theorem kmedian_pp_tight_ratio (k : ℕ) (hk : 1 ≤ k) (Δ : ℕ) :
    (∀ (M : Type u) [MetricSpace M] (n : ℕ), 0 < n → ∀ X : Fin n → M,
      expectedCost X 1 k Δ ≤ 2 * B k Δ * opt X 1 k) ∧
    (∃ (Ms : ℕ → Type) (inst : ∀ m, MetricSpace (Ms m)) (N : ℕ → ℕ)
      (X : ∀ m, Fin (N m) → Ms m),
      StrictMono N ∧
      (∀ m, 0 < @opt (Ms m) (inst m) (N m) (X m) 1 k) ∧
      Filter.Tendsto
        (fun m => @expectedCost (Ms m) (inst m) (N m) (X m) 1 k Δ /
          @opt (Ms m) (inst m) (N m) (X m) 1 k)
        Filter.atTop (nhds (2 * B k Δ))) := by sorry

end KMedianPP.Tight
