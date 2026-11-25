-- Prove2me | Theorems.Thm_NearLinearRSP_TwoResources_Supplement_deterministic_multi_resource_rsp
-- name    : NearLinearRSP.TwoResources.Supplement.deterministic_multi_resource_rsp
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T17:22:48.97122+00:00
-- url     : https://prove2.me/theorems/2f48645d-1c01-4776-b273-0486110a17be
-- title:
--   Theorem 2 (companion theorem; not used in the proof of the goal) — deterministic k-resource RSP
-- statement:
--   For every fixed integer $k\ge2$, there exist finite deterministic preprocessing and retrieval programs and a positive constant $K_k$, chosen before every graph, resource instance and accuracy. An instance consists of a finite directed graph with $n$ vertices and $m$ edges, source $s$, nonnegative real objective lengths $\ell$, nonnegative real costs $c_j$ and budgets $C_j$ for $j=0,\ldots,k-2$. Cycles, zero weights, zero budgets and isolated vertices are allowed. All $k$ accuracy coordinates equal $0<\varepsilon<1$.
--
--   Let $W$ be the ratio of the largest to smallest positive objective length, or one if no length is positive. Preprocessing executes at most
--   $$
--   K_k\,\frac{\max(1,m)(1+\log\max(2,n))(1+\log(\max(2,n)W))}{\varepsilon^{4k+1}}
--   $$
--   unit instructions and produces a compact snapshot of the computed multidimensional tables, parent labels, ranks, generating functions and target certificates. There is exactly one suppressed $\log n$ factor. The coefficient and programs may depend on $k$ and on nothing else.
--
--   Simultaneously for every target with an exactly feasible path, the snapshot reports a finite upper distance $d_t$ and permits deterministic retrieval of an actual directed path $P_t:s\leadsto t$ such that
--   $$
--   \ell(P_t)\le d_t\le(1+\varepsilon)\ell(R)
--   \quad\text{for every }R:s\leadsto t\text{ with }\forall j,\ c_j(R)\le C_j,
--   \qquad
--   \forall j,\ c_j(P_t)\le(1+\varepsilon)C_j.
--   $$
--   Every reported finite distance certifies such a returned path, and every returned path is valid and obeys every relaxed budget. Targets with only relaxed-feasible paths may receive answers; exact infeasibility detection is not required. The source returns $[s]$ at distance zero. No optimum, table correctness, algorithm success or runtime bound is an input hypothesis.
--
--   Set $\delta=\varepsilon/4$ and $q=\lceil512k/\delta^2\rceil$. A query on the shared snapshot takes at most $K_k(q+1)^k(|P_t|+1)$ charged instructions, including virtual ticks, coordinate scans and path writing; an absent answer uses $|P_t|=0$. The table construction has at most $q^k$ layers and $q^k$ relaxation summands per edge, giving per-guess work $O_k(\max(1,m)q^{2k}\log\max(2,n))$. Positive guesses number $O(\log(nW)/\delta)$; the additional zero-objective call is within the displayed total bound. These per-call counts explain the explicit normalization of the headline asymptotic bound, not additional hypotheses.
--
--   This companion theorem extends the base bicriteria result to all fixed numbers of independently constrained resources. Its proof must establish the k-dimensional construction and charged implementation; the base two-dimensional correctness lemmas are not assumed to prove these new facts.
--
--   **Formalization Note** The computational model is the unchanged published primitive real RAM: real constants/copies, exact field operations, comparisons and exp each cost one; natural constants/copies, addition, truncated subtraction, comparisons, jumps and halt each cost one. Every indirect load, store and input-cell read costs one; arithmetic operand register access is included in that instruction. There is no floor, real-to-integer conversion, logarithm, heap, distribution or whole-table instruction. Programs must implement and charge coefficient generation, all loops and memory operations. The displayed ceil and logarithms are semantic specifications and bounds, not oracle instructions. Real arithmetic with a parallel counter can generate Poisson coefficients from exp. Zero means give point mass at zero. Passing a snapshot to a query incurs no memory copy. Successful execution, uniform preprocessing time, deterministic retrieval time and all approximation clauses are theorem conclusions. Program witnesses and proofs are left open in this statements pass.
--
--   Differences from the source:
--   - reading: infinite-precision real-RAM computation with Poisson coefficients and generating functions → the published unit-cost exact arithmetic, comparison, exp, register, input, memory and control instructions; reason: this is the base mission computational-model reading; no floor, conversion, logarithm or algorithm oracle is added
--   - encoding: for any fixed k at least two, O-tilde(m log(nW)/epsilon^(4k+1)) with one suppressed log n → for each k at least two choose finite programs and one positive K_k before all instances and epsilon, bounding max(1,m)*(1+log(max(2,n)))*(1+log(max(2,n)*W))/epsilon^(4k+1); reason: total small-instance conventions preserve the exact exponent and logarithmic factors, while allowing dependence only on fixed k
--   - encoding: one objective and k-1 independently constrained nonnegative real resources → published finite Digraph and multiplicity-aware path sums, NNReal resources indexed by Fin(k-1), and a comparator satisfying every original budget; reason: the representation preserves every source instance and zero optimum; the ENNReal optimum is infinity on an empty feasible family
--   - encoding: q=A_k*epsilon^-2 for a sufficiently large fixed A_k and k clocks → delta=epsilon/4, q=ceil(512k/delta^2), acceptance 1/4 and potential coefficient 1/(8k) on each retained coordinate; reason: union tails at most 9/(512k) and 18/(512k), and the potential exponent at least 512k/27, suffice for all k factors without an invented global runtime numeral
--   - encoding: nonnegative resources with minor zero-weight bookkeeping → filter edges positive in zero-budget coordinates, omit those clocks, run the remaining clocks on the zero-length subgraph with an objective threshold of one, and use ordinary Dijkstra if no positive budgets remain; reason: no original instance is excluded and multiple simultaneous constraints remain enforced in the zero-objective branch
--   - encoding: geometric threshold guesses and accuracy rescaling → original a*(1+delta)^j through the first value at least n*b, W=b/a or one if no positive length, and reported upper distance (1+delta)*L; reason: (1+delta)^2 is at most 1+epsilon; all-zero objective instances use only the zero-objective branch
--   - encoding: deterministic queue and retrieval choices with unspecified ties → decreasing lexicographic tick layers, first-minimum ties, strict relaxation, extraction ranks, filtered self-loops and a finite retrieval fuel; reason: these fix the permitted deterministic choices and make zero-increment progress and virtual ticks explicit without assuming success
--   - encoding: compact simultaneous single-source output and deterministic path retrieval → a sparse snapshot of actual computed tables and certificates, all-target comparator and witness conclusions, and a query bound K_k*(q+1)^k*(path vertex count+1); reason: isolated targets are implicit, exact-feasible targets must be supplied, relaxed-feasible answers are allowed, and path writing is charged separately without copying the snapshot
-- source:
--   Vikrant Ashvinkumar, STOC 2027 submission #289 (October 2026), p.3, Theorem 2; definition of k resources p.2; zero-weight and real-RAM convention p.3; proof sketch Appendix B p.14 extending Sections 4–6 pp.6–12

import Definitions.Def_NearLinearRSP_TwoResources_Supplement_RAM

set_option autoImplicit false

namespace NearLinearRSP.TwoResources.Supplement

/-- Theorem 2, p.3; Appendix B p.14, extending Sections 4-6.
All k factors and the exponent 4k+1, uniformly over all nonnegative inputs.
The finite programs and coefficient may depend on fixed k, and on nothing else. -/
theorem deterministic_multi_resource_rsp :
    ∀ k : ℕ, 2 ≤ k →
      ∃ preprocessing retrieval : Program, ∃ K : ℝ, 0 < K ∧
        ∀ (I : MultiInstance k) (ε : ℝ), 0 < ε → ε < 1 →
          ∃ (steps : ℕ) (snapshot : RAMState),
            Execution preprocessing (multiInput I ε) initialState snapshot steps ∧
            (steps : ℝ) ≤ K * multiScale I ε ∧ EncodesMultiOutput I ε snapshot ∧
            ∀ t : ℕ, t < I.graph.n →
              multiDistance snapshot t = selectedDistance I ε t ∧
              (∃ (querySteps : ℕ) (out : RAMState),
                Execution retrieval (multiInput I ε) (multiQueryStart snapshot t) out querySteps ∧
                multiQueryPath out = selectedPath I ε t ∧
                (querySteps : ℝ) ≤ K * multiRetrievalScale k ε (selectedPath I ε t)) ∧
              (∀ d : ℝ, multiDistance snapshot t = some d →
                ∃ P : List ℕ, selectedPath I ε t = some P ∧
                  RelaxedPath I ε t P ∧ pathWeight I.length P ≤ d ∧
                  ∀ R : List ℕ, ExactFeasible I t R → d ≤ (1 + ε) * pathWeight I.length R) ∧
              ((∃ R : List ℕ, ExactFeasible I t R) →
                (multiDistance snapshot t).isSome = true) ∧
              (∀ P : List ℕ, selectedPath I ε t = some P → RelaxedPath I ε t P) := by sorry

end NearLinearRSP.TwoResources.Supplement
