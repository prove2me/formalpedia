-- Prove2me | Theorems.Thm_NNPartTree_claim_6_3
-- name    : NNPartTree.claim_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:11:52.561121+00:00
-- url     : https://prove2.me/theorems/a86aa9a3-d219-4163-b922-be8164e875ff
-- title:
--   Claim 6.3, pp.24–25 (corrected: corrected oracle, every point of mass $\le\gamma/2$, restored $1/\beta_1$) — GreedyTree terminates with $O(1/(\beta_1\gamma))$ nodes
-- statement:
--   There are absolute constants $c_1,c$ with the following. Let $P$ be injective, $\mathcal D$ a nearest neighbor distribution with a perfect $1/3$-balanced halfspace tree, $0<\beta_1\le1/3$, $\gamma,\delta\in(0,1)$, $\varepsilon_c>0$, $R\ge c/(\beta_1\gamma)$ and $J\ge c\log(1/(\beta_1\gamma))/\beta_1$, $O$ a $(\beta_1,1/3,R,J,\varepsilon_c)$-balanced cut oracle, and every point of mass at most $\gamma/2$. With the blocks of size $m$ between $x$ and $2x$, $x=c_1\log(1/(\delta\beta_1\gamma))/\gamma$, the following holds with probability at least $1-\delta$: GreedyTree terminates at a tree $T$, all invocations of TestMass succeed, $T$ has at most $c/(\beta_1\gamma)$ internal nodes and tests,
--   $$\sum_{u\text{ internal}}|P^u|\le\frac{c\,n\log(1/(\beta_1\gamma))}{\beta_1},\qquad\#\text{samples}\le\frac{c\log(1/(\delta\beta_1\gamma))}{\beta_1\gamma^2}.$$
--
--   Differences from the source:
--   - correction: O a balanced cut oracle of Definition 6.5 → the corrected oracle, whose balance holds when some (R, J)-function has balance at least β₀, with R and J as in Lemma 6.4; reason: Definition 6.5 is unsatisfiable on a point-mass marginal, so the claim would be vacuous
--   - correction: no condition on point masses → every point has D_nn mass at most γ/2; reason: needed with the corrected oracle: d = 1, P = {−1, 1}, self-pairs with masses 2/3, 1/3, T★ the cut at 0, γ < 1/3; the child holding −1 has mass ≥ 2γ, so it tests Large, D^(u) has a point-mass marginal, the oracle may return a constant, one child repeats the region and GreedyTree does not terminate
--   - correction: time O(nτ log(1/(β₁γ)) + log(1/(δβ₁γ))/γ²) and O(log(1/(δβ₁γ))/γ²) samples → factors 1/β₁ as derived on p.25; reason: the printed bound fails uniformly in β₁: peeling a β₁-fraction at each node needs ≳ log(1/γ)/β₁ tests with fresh samples each; both forms agree at constant β₁
--   - encoding: time and samples, excluding O → counts: internal nodes, tests, Σ|P^u| cut evaluations of cost τ, and tests × m samples; reason: time is τ × (count) + (count)
--   - encoding: TestMass with parameter δ′ = Θ(δβ₁γ) on fresh samples per call → independent blocks indexed by address, m within a factor 2 of c₁ log(1/δ′)/γ; reason: each address is tested at most once, so the law is the same; the failure set is bounded in outer measure
-- source:
--   Khanna, Padaki, Waingarten, Learning Partition Trees for Nearest Neighbor Search, arXiv:2607.09909 (held copy of 2026-11-03, sha256 d32992f2…), Claim 6.3, pp.24–25; proof p.25; GreedyTree, p.24

import Mathlib
import Definitions.Def_NNPartTree_GreedyTree

open MeasureTheory

namespace NNPartTree

/-- **Claim 6.3**, pp.24–25 (corrected). S. Khanna, A. Padaki, E. Waingarten, *Learning Partition Trees for Nearest Neighbor Search*, arXiv:2607.09909 (held copy of 2026-11-03, sha256 d32992f2…).

With probability at least `1 − δ`, GreedyTree terminates, all invocations of TestMass succeed, there are at most `c/(β₁γ)`
calls to `O` and to TestMass, the partition work is `Σ_{u internal} |P^u| ≤ c n log(1/(β₁γ))/β₁` cut evaluations, and at most
`c log(1/(δβ₁γ))/(β₁γ²)` samples are used.

**Formalization Note.** (1) The oracle is the corrected one of `IsBalancedCutOracle`, for `R, J` as in Lemma 6.4, and every point has
mass at most `γ/2`. Counterexample without that condition: `d = 1`, `P = {−1, 1}`, `D` on self-pairs with masses `2/3, 1/3`, `T★` the cut
at `0`, `γ < 1/3`: the child holding `−1` has mass `2/3 ≥ 2γ`, and `D^{(u)}` has a point-mass marginal, so a corrected oracle may return
a constant, one child repeats the region and GreedyTree does not terminate. (2) The printed time and sample bounds omit the `1/β₁` the
proof derives on p.25; with `β₁ → 0` peeling a `β₁`-fraction at each node uses `≳ log(1/γ)/β₁` tests, so the printed bound fails uniformly in
`β₁`. Costs are counts: `τ` per cut evaluation. `m` is the block size of TestMass, of order `log(1/δ′)/γ` for `δ′ = Θ(δβ₁γ)`. -/
theorem claim_6_3 : ∃ c₁ c : ℝ, 0 < c₁ ∧ 0 < c ∧
    ∀ (n d : ℕ) (P : Fin n → Pt d), Function.Injective P →
    ∀ (D : Measure (Pt d × Pt d)) [IsProbabilityMeasure D], IsNNDist P D →
    (∃ Tstar : CutTree d, IsPerfectTree P D (1 / 3) Tstar) →
    ∀ (β₁ γ δ ε_c C_O : ℝ) (R J : ℕ) (O : Measure (Pt d × Pt d) → Pt d → ℝ),
    0 < β₁ → β₁ ≤ 1 / 3 → 0 < γ → γ < 1 → 0 < δ → δ < 1 → 0 < ε_c →
    c / (β₁ * γ) ≤ R → c * Real.log (1 / (β₁ * γ)) / β₁ ≤ J →
    IsBalancedCutOracle O β₁ (1 / 3) R J ε_c C_O →
    (∀ i, marginalY D {P i} ≤ ENNReal.ofReal (γ / 2)) →
    ∀ m : ℕ, c₁ * Real.log (1 / (δ * β₁ * γ)) / γ ≤ m →
    m ≤ 2 * (c₁ * Real.log (1 / (δ * β₁ * γ)) / γ) →
    blockLaw D m {ω | ¬ ∃ T : CutTree d, IsGreedyRun O D γ ω T ∧ TestsCorrect D γ ω T ∧
        (T.internalAddrs.length : ℝ) ≤ c / (β₁ * γ) ∧
        (T.nodeAddrs.length : ℝ) ≤ c / (β₁ * γ) ∧
        ((T.internalAddrs.map fun u => {i | P i ∈ T.region u}.ncard).sum : ℝ) ≤
          c * n * Real.log (1 / (β₁ * γ)) / β₁ ∧
        ((T.nodeAddrs.length * m : ℕ) : ℝ) ≤ c * Real.log (1 / (δ * β₁ * γ)) / (β₁ * γ ^ 2)} ≤
      ENNReal.ofReal δ := by sorry

end NNPartTree
