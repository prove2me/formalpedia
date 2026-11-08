-- Prove2me | Theorems.Thm_NNPartTree_theorem_4
-- name    : NNPartTree.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:12:25.614677+00:00
-- url     : https://prove2.me/theorems/def635c8-9b72-4076-a8ce-13ead17c73cf
-- title:
--   Theorem 4, p.27 — polynomial-time learner of an $O(nd)$-space, $o(nd)$-time nearest neighbor structure when a perfect $1/3$-balanced halfspace tree exists
-- statement:
--   This is the main theorem of the paper.
--
--   There are programs $\mathrm{Learn}$ and $\mathrm{Qry}$ and constants $C,K$ such that for all $c_1>0$ and $c_2\in\mathbb R$ there is a function $\eta(n)\to0$ with the following property. Let $n,d\ge1$ with $d\le(1+\log n)^{c_2}$, let $P=\{p_1,\dots,p_n\}\subset\mathbb R^d$ be $n$ distinct points, and let $\mathcal D$ be a nearest neighbor pair distribution for $P$ such that
--
--   1. for all $\varepsilon_a>0$ and $R,J\in\mathbb N$, $\mathcal D$ has $(R,J)$-halfspace approximation degree $k(\varepsilon_a)\le(R\cdot2^J/\varepsilon_a)^{c_1}$;
--   2. $\mathcal D$ admits a perfect $1/3$-balanced halfspace tree $T^\star$.
--
--   Given $P$ and sample access to $\mathcal D$, $\mathrm{Learn}$ halts within $C(nd)^K$ work on every run, and with probability at least $1-\eta(n)$ over its coins and samples it leaves a data structure with
--   $$\text{at most }Cnd\text{ nonzero cells};\qquad\text{query work at most }\eta(n)\,nd\text{ on every }q;\qquad\Pr_{(q,p^\star)\sim\mathcal D}[\text{answer not a nearest neighbor of }q]\le\eta(n).$$
--
--   So a data structure of linear space and sublinear query time can be learned from samples, competing with the best balanced halfspace tree.
--
--   **Formalization Note** The failure set of the run is bounded in outer measure, and $\mathrm{Qry}$ has neither coins nor samples.
--
--   Differences from the source:
--   - reading: "There exists a polynomial-time algorithm", no machine named → the sampling real RAM `NNPartTree.Machine`, with integer memory, and work ≤ C(nd)^K on every run; reason: the page names no machine; integer memory is needed, since with pointers moving by ±1 a query of work o(nd) cannot write most indices below n (d = 1, D uniform on self-pairs is then a counterexample)
--   - reading: polynomial-time, O(nd), o(nd), 1 − o(1), d = polylog(n), "there is a constant c₁" → ∃ Learn, Qry, C, K, then ∀ c₁ > 0, ∀ c₂, ∃ η → 0, then the instance, with d ≤ (1 + log n)^{c₂}; reason: the printed order has the algorithm before c₁; η depending only on c₁, c₂ makes o(·) uniform over instances, since otherwise it is empty for each instance; 1 + log avoids log 1 = 0
--   - reading: uses space O(nd) → at most C·n·d nonzero cells in the memory at the halt of Learn; reason: the structure of p.28; cells written would count working memory
--   - reading: a perfect 1/3-balanced halfspace tree T★ → the tree of §1, p.4, with n leaves and T(p) = p; reason: bare Definition 6.1 does not constrain leaves, so a single leaf would be vacuously perfect and the hypothesis empty; the proof, p.25, needs §1's leaves
--   - reading: finds a nearest neighbor in time o(nd) → pointer register 0 is an index of a minimizer, and work ≤ η(n)nd on every q with a valid index; reason: under a tie p★ is not a function of q; the query is deterministic, as in the proof (Claim 6.1)
--   - generalization: §6 induced D with p★ = NN(q) → §1 D on ℝ^d × P with p★ almost surely a minimizer; reason: the theorem says "a nearest neighbor pair distribution", and the induced case is an instance
--   - encoding: P ⊂ ℝ^d of n points, D over ℝ^d × P → injective P : Fin n → ℝ^d, D a law on ℝ^d × ℝ^d with `IsNNDist`; a sample is one vector of ℝ^{2d}; reason: same instances; layouts are fixed in `NNPartTree.Learner`
--   - encoding: moments in the approximation degree → `∫⁻` in [0, ∞], degree compared in ℝ; failure set bounded in outer measure; reason: Bochner integrals would be 0 on non-integrable data; the event quantifies over q
-- source:
--   Khanna, Padaki, Waingarten, Learning Partition Trees for Nearest Neighbor Search, arXiv:2607.09909 (held copy of 2026-11-03, sha256 d32992f2…), Theorem 4, p.27; proof pp.27–28; §1, pp.3–4

import Mathlib
import Definitions.Def_NNPartTree_Learner

open MeasureTheory Filter Topology

namespace NNPartTree

/-- **Theorem 4** (Formalization of Theorem 1), p.27. S. Khanna, A. Padaki, E. Waingarten, *Learning Partition Trees for Nearest Neighbor Search*, arXiv:2607.09909 (held copy of 2026-11-03, sha256 d32992f2…).

There are programs `Learn`, `Qry` and constants `C, K`, chosen before everything else, such that for all `c₁ > 0` and `c₂` there is `η → 0` with the
following. For all `n, d ≥ 1` with `d ≤ (1 + log n)^{c₂}`, every injective `P : [n] → ℝᵈ` and every nearest neighbor pair distribution `D` with
`(R, J)`-halfspace approximation degree `k(ε) ≤ (R · 2^J/ε)^{c₁}` that admits a perfect `1/3`-balanced halfspace tree:
`Learn` halts within `C (nd)^K` work on every run, and with probability at least `1 − η(n)` over its coins and samples it leaves a data structure of space
at most `C n d` on which `Qry`, on every `q`, halts within `η(n) n d` work, with a valid index, and which finds a nearest neighbor with probability at
least `1 − η(n)` over `(q, p★) ∼ D`.

**Formalization Note.** The page names no machine; this is `NNPartTree.Machine`, a sampling real RAM with integer memory, and `Qry` has neither coins nor
samples. The quantifier order follows the page: the algorithm comes before `c₁`, and `η` depends only on `c₁, c₂`, so `o(·)` is uniform over instances;
otherwise the statement would be empty for each single instance. `polylog(n)` is `(1 + log n)^{c₂}`, the `1 +` avoiding `log 1 = 0`. Polynomial time is `(nd)^K`,
because `K` precedes `c₂` and the input has `nd` numbers. The perfect tree is that of §1, p.4. The condition `cost_D(T★) ≤ δ_s⁶` used on p.28 is not in the
theorem and is not assumed. The failure set is bounded in outer measure. -/
theorem theorem_4 : ∃ Learn Qry : Program, Admissible Learn ∧ DetProgram Qry ∧ ∃ C K : ℕ,
    ∀ c₁ : ℝ, 0 < c₁ → ∀ c₂ : ℝ, ∃ η : ℕ → ℝ, Tendsto η atTop (𝓝 0) ∧
      ∀ n d : ℕ, 1 ≤ n → 1 ≤ d → (d : ℝ) ≤ (1 + Real.log n) ^ c₂ →
      ∀ P : Fin n → Pt d, Function.Injective P →
      ∀ (D : Measure (Pt d × Pt d)) [IsProbabilityMeasure D],
        IsNNDist P D → HasDegreeBound D c₁ → (∃ T : CutTree d, IsPerfectTree P D (1 / 3) T) →
        (∀ ω : (ℕ → Bool) × (ℕ → Pt (2 * d)), ∃ st, IsFinal Learn (2 * d) (learnInput P) ω st ∧
          (st.work : ℝ) ≤ C * ((n : ℝ) * d) ^ K) ∧
        sampleSpace D {ω | ¬ ∃ st, IsFinal Learn (2 * d) (learnInput P) ω st ∧
            IsGoodStructure Qry P D C (η n) st} ≤ ENNReal.ofReal (η n) := by sorry

end NNPartTree
