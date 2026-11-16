-- Prove2me | Theorems.Thm_MinSumFPT_Supplement_theorem_40
-- name    : MinSumFPT.Supplement.theorem_40
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:19:43.386791+00:00
-- url     : https://prove2.me/theorems/2f69ab8e-624a-42c7-9d57-0a74a00e7222
-- title:
--   Theorem 40 — a $2^{(k/\varepsilon)^\alpha}2^{n^\alpha}$-time min-sum approximation scheme decides 3-SAT in time $2^{N^{\alpha+o(1)}}$
-- statement:
--   Fix a constant $\alpha\in(0,1)$. Suppose there is an algorithm that, for every $n\ge1$, $1\le k\le n$, $\varepsilon\in(0,1)$ and every metric $d$ on $n$ points, computes a clustering of the points into $k$ clusters of cost at most $(1+\varepsilon)\,\mathrm{OPT}_k(d)$ in time
--   $$
--   K\cdot 2^{(k/\varepsilon)^\alpha}\cdot 2^{n^\alpha}.
--   $$
--   Then for every constant $c$ there are an algorithm and a function $g$ with $g(N)\to0$ such that the algorithm decides the satisfiability of every 3-CNF formula on $N$ variables with at most $cN$ clauses in time
--   $$
--   2^{N^{\alpha+g(N)}}\qquad(N\ge2).
--   $$
--
--   Here $\mathrm{OPT}_k(d)$ is the least k-minsum cost $\sum_i\sum_{x,y\in C_i}d(x,y)$. The page adds that the conclusion contradicts the Almost Exponential Time Hypothesis; so under that hypothesis the doubly exponential dependence on $k$ in Theorem 1 cannot be brought down to $2^{(k/\varepsilon)^{\alpha}}$ for any $\alpha<1$, even at running time $2^{n^\alpha}$ in $n$.
--
--   **Formalization Note** The approximation algorithm is one admissible program of `MinSumFPT.Machine` with inputs $n,k,\varepsilon$ ($\delta=0$) that reads the metric through the distance oracle, writes the labelling at the output addresses and must succeed on every random tape. The decision procedure is an admissible program run on the integer encoding of the formula (`MinSumFPT.Supplement.CNF3`), answering $1$/$0$ on every random tape; for $N\le1$, where $N^{\alpha+g(N)}$ cannot grow, it must answer within a constant number of steps.
--
--   Differences from the source:
--   - reading: a 2^{(k/ε)^α}·2^{n^α} time (1+ε)-approximation algorithm → one admissible program of MinSumFPT.Machine (inputs n, k, ε, δ = 0) reading the metric through the distance oracle and succeeding on every random tape; reason: the page names no machine; the mission's model of Theorem 1, where computing d(x, y) is a single operation; 'algorithm' read deterministically, no success probability added
--   - generalization: for every n, k, ε → for every n ≥ 1, 1 ≤ k ≤ n, ε ∈ (0, 1); reason: a weaker hypothesis: the proof runs the algorithm only at k = n/3 and ε = δ₀² < 1
--   - generalization: time 2^{(k/ε)^α}·2^{n^α} → time K·2^{(k/ε)^α}·2^{n^α} for some constant K; reason: a weaker hypothesis; the constant is absorbed in the conclusion's o(1)
--   - encoding: a (1+ε)-approximate k-minsum clustering → a labelling σ : Fin n → Fin k with labCost d σ ≤ (1 + ε)·optCost d k; reason: the base mission's convention: ordered pairs and empty clusters allowed, which changes neither the ratio nor the optimum
--   - reading: 3-CNF formulas on N variables and O(N) clauses → for every constant c, formulas with at most c·N clauses; the decider and g may depend on c; reason: O(N) is a bound c·N for a constant c
--   - generalization: 3-CNF formulas → CNF formulas with at most three literals per clause, including empty and tautological clauses; reason: covers every 3-CNF formula; the extra clauses are decided trivially
--   - reading: decided in 2^{N^{α+o(1)}} time → one admissible program answering 1/0 on the integer encoding, on every tape, within 2^{N^{α+g(N)}} steps for N ≥ 2 with g → 0, and within a constant K' for N ≤ 1; reason: o(1) is a function tending to 0; for N ≤ 1 the expression N^{α+g(N)} is at most 1 and no bound in this form can read the input
-- source:
--   Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, A Fixed Parameter Sublinear Time Approximation Scheme for Metric Min-Sum Clustering, arXiv:2610.15148 (held version of November 2, 2026, sha256 12e81235…), Theorem 40, p.48 (PDF p.49); k-minsum cost, §1, p.1

import Mathlib
import Definitions.Def_MinSumClust_IsMetric
import Definitions.Def_MinSumFPT_Machine
import Definitions.Def_MinSumFPT_labCost
import Definitions.Def_FasterWCTFPTAS_Main_Supplement_CNF
import Definitions.Def_MinSumFPT_Supplement_InputMachine
import Definitions.Def_MinSumFPT_Supplement_CNF3
set_option autoImplicit false
open Filter Topology
open scoped Classical

namespace MinSumFPT.Supplement

/-- Theorem 40 (Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, *A Fixed Parameter Sublinear Time Approximation Scheme for Metric Min-Sum Clustering*, arXiv:2610.15148 (held version of November 2, 2026, sha256 12e81235…), Theorem 40, p.48): for every constant `α ∈ (0, 1)`, suppose there is a
`2^{(k/ε)^α} · 2^{n^α}` time `(1 + ε)`-approximation algorithm for metric k-minsum clustering, for
every `n, k, ε` and every metric on `n` points. Then the satisfiability of 3-CNF formulas on `N`
variables and `O(N)` clauses can be decided in `2^{N^{α+o(1)}}` time.

**Formalization Note.** The hypothesis is one admissible program `P` of `MinSumFPT.Machine`
(inputs `n, k, ε`, `δ = 0`; the metric through the distance oracle) and a constant `K` such that
for all `n ≥ 1`, `1 ≤ k ≤ n`, `ε ∈ (0, 1)` and every metric `d` on `Fin n`, on every tape `P`
halts within `K · 2^{(k/ε)^α} · 2^{n^α}` steps with a labelling `σ : Fin n → Fin k` of cost at most
`(1 + ε) · OPT_k(d)`. The conclusion: for every constant `c` there are an admissible program `Q`
(run on the explicit input `encodeCNF F`), a function `g → 0` and a constant `K'` such that on
every 3-CNF formula `F` on `N` variables with at most `c · N` clauses `Q` answers its
satisfiability (output `1`/`0`) on every tape within `2^{N^{α + g(N)}}` steps when `N ≥ 2`, and
within `K'` steps when `N ≤ 1` (where `N^{α+g(N)}` cannot grow). -/
theorem theorem_40 (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (hA : ∃ P : Program, Admissible P ∧ ∃ K : ℝ,
      ∀ (n k : ℕ) (ε : ℝ) (d : Fin n → Fin n → ℝ), 1 ≤ n → 1 ≤ k → k ≤ n → 0 < ε → ε < 1 →
        MinSumClust.IsMetric d → ∀ ω : ℕ → ℝ, ∃ (t : ℕ) (σ : Fin n → Fin k),
          OutputsLabelling (run P n k ε 0 d ω t) σ ∧
          ((run P n k ε 0 d ω t).work : ℝ) ≤
            K * (2 : ℝ) ^ (((k : ℝ) / ε) ^ α) * (2 : ℝ) ^ ((n : ℝ) ^ α) ∧
          labCost d σ ≤ (1 + ε) * optCost d k) :
    ∀ c : ℝ, ∃ Q : Program, Admissible Q ∧ ∃ (g : ℕ → ℝ) (K' : ℝ), Tendsto g atTop (𝓝 0) ∧
      ∀ F : FasterWCTFPTAS.Main.Supplement.CNF, Is3CNF F →
        (F.clauses.length : ℝ) ≤ c * F.numVars →
        AnswersWithin Q (encodeCNF F) [] (decide F.Satisfiable)
          (if 2 ≤ F.numVars then (2 : ℝ) ^ ((F.numVars : ℝ) ^ (α + g F.numVars)) else K') := by sorry

end MinSumFPT.Supplement
