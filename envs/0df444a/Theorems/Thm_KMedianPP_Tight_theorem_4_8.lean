-- Prove2me | Theorems.Thm_KMedianPP_Tight_theorem_4_8
-- name    : KMedianPP.Tight.theorem_4_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:02:42.990894+00:00
-- url     : https://prove2.me/theorems/92c30703-7b59-40a7-b41e-db6cf2267b62
-- title:
--   Theorem 4.8 — instances of increasing size on which the ratio of D-sampling with $k+\Delta$ centers tends to $2B_{k,\Delta}$
-- statement:
--   For fixed integers $k\ge1$ and $\Delta\ge0$ there is an infinite sequence of metric k-median instances (metric spaces $M_m$ with input multisets $X_m$ of $N_m$ points), with $N_m$ strictly increasing and $\mathrm{OPT}_m>0$, on which the approximation ratio of D-sampling ($\ell=1$) with $k+\Delta$ centers approaches $2B_{k,\Delta}$:
--   $$\frac{\mathbb E[\mathrm{cost}(C_{\mathrm{final}})]}{\mathrm{OPT}}\ \longrightarrow\ 2B_{k,\Delta}.$$
--
--   Differences from the source:
--   - encoding: an infinite sequence of metric k-median instances → types `Ms m` with `MetricSpace (Ms m)` instances and inputs `X m : Fin (N m) → Ms m`, m ∈ ℕ; reason: each instance is a metric space with a finite multiset input
--   - encoding: "with an increasing number of input points" → `StrictMono N`; reason: strictly increasing sizes, as in the proof (n → ∞)
--   - reading: "the approximation ratio of D-sampling with k + Δ centers approaches 2B_{k,Δ}" → `0 < opt (X m) 1 k` for every m and `Tendsto (fun m => expectedCost (X m) 1 k Δ / opt (X m) 1 k) atTop (𝓝 (2 * B k Δ))`; reason: on one instance the ratio is E[cost(C_final)]/OPT, which needs OPT > 0; the proof's instances have OPT > 0
--   - encoding: OPT = the minimum cost over k-point solutions in M → `opt X 1 k` = infimum of cost(X, C) over C : Finset M with 1 ≤ |C| ≤ k; reason: k points possibly coinciding = a nonempty set of at most k points; the infimum equals the minimum when attained, and the set is nonempty and bounded below by 0
--   - encoding: E[cost(C_final)] over the algorithm's random choices → `expectedCost X ℓ k Δ`: (1/n) Σ_i of the exact recursion `expFinalCostFrom` over the k + Δ − 1 remaining D^ℓ-samples from {x_i}; reason: the exact finite expectation of the same Markov chain
--   - encoding: footnote 4: if cost(C) = 0 the algorithm terminates → the expectation recursions return the current value when `totalCost = 0`; reason: same process; the next-sample law is undefined there
--   - encoding: metric spaces of any size → the instances live in `Type` (universe 0); reason: an existential: instances in Type 0 are instances
-- source:
--   Kaplan, Naori, Tight Bounds for k-Median++ and Improved Bounds for k-Means++, STOC 2027 submission (manuscript sha256 f017529e…), p. 24 (PDF 26), Theorem 4.8; proof pp. 24–25 (PDF 26–27)

import Mathlib
import Definitions.Def_KMedianPP_Tight_Sampling
import Definitions.Def_KMedianPP_Tight_EqualMass

set_option autoImplicit false

namespace KMedianPP.Tight

/-- Theorem 4.8 (p. 24): for fixed integers `k ≥ 1` and `Δ ≥ 0` there is an infinite sequence of
metric k-median instances with a strictly increasing number of input points (and `OPT > 0`) on
which the approximation ratio `E[cost(C_final)] / OPT` of D-sampling with `k + Δ` centers tends to
`2 B_{k,Δ}`. -/
theorem theorem_4_8 (k : ℕ) (hk : 1 ≤ k) (Δ : ℕ) :
    ∃ (Ms : ℕ → Type) (inst : ∀ m, MetricSpace (Ms m)) (N : ℕ → ℕ)
      (X : ∀ m, Fin (N m) → Ms m),
      StrictMono N ∧
      (∀ m, 0 < @opt (Ms m) (inst m) (N m) (X m) 1 k) ∧
      Filter.Tendsto
        (fun m => @expectedCost (Ms m) (inst m) (N m) (X m) 1 k Δ /
          @opt (Ms m) (inst m) (N m) (X m) 1 k)
        Filter.atTop (nhds (2 * B k Δ)) := by sorry

end KMedianPP.Tight
