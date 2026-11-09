-- Prove2me | Theorems.Thm_NearLinearRSP_TwoResources_deterministic_bicriteria_rsp
-- name    : NearLinearRSP.TwoResources.deterministic_bicriteria_rsp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:25:25.565014+00:00
-- url     : https://prove2.me/theorems/89a66c92-1b34-41a7-93bd-4a6e8f580fe8
-- title:
--   Theorem 1 — deterministic near-linear single-source bicriteria RSP
-- statement:
--   There exist fixed finite deterministic real-RAM programs for preprocessing and witness retrieval, and one positive absolute constant $K$, uniformly for every finite directed graph with $n$ vertices and $m$ distinct ordered-pair edges, source $s$, nonnegative real edge lengths $\ell$ and costs $c$, budget $C\ge0$, and accuracy $0<\varepsilon<1$.
--
--   Preprocessing constructs a compact all-target data structure in at most
--   $$
--   K\,\frac{\max(1,m)(1+\log\max(2,n))(1+\log(\max(2,n)W))}{\varepsilon^9}
--   $$
--   unit instructions. Here $W$ is the ratio of the largest to smallest positive edge length, or one if all lengths are zero. There is exactly one suppressed $\log n$ factor on nontrivial inputs.
--
--   For every target having an exactly $C$-feasible path, the stored distance $d_t$ certifies a deterministically retrievable directed $s$–$t$ path $P_t$, and
--   $$
--   \ell(P_t)\le d_t\le(1+\varepsilon)\operatorname{OPT}_C(t),\qquad
--   c(P_t)\le(1+\varepsilon)C.
--   $$
--   Every reported finite distance certifies a returned path with that upper length and relaxed budget, including targets that happen to have only relaxed-feasible paths. Every returned witness is valid. The guarantee is simultaneous for all targets and compares with the original budget. An infeasible target may have a relaxed-feasible answer; no exact infeasibility oracle is asserted.
--
--   The snapshot encodes the tables actually constructed by Section 4 and the two boundary shortest-path trees. Each target chooses its least accepted normalized guess, retains the same table for its path, and reports the extra inner length factor. With $\delta=\varepsilon/4$ and $q=\lceil512/\delta^2\rceil$, a witness query takes at most $K(q+1)^2(|P_t|+1)$ charged instructions, including path writing. An absent path has length zero in this query bound. Listing all target paths is separate from preprocessing.
--
--   **Formalization Note** Exact real $+,-,\times,\div$, comparisons $<$ and $=$, constants, copies and $\exp$ each cost one instruction. Natural constants, copies, $+$, truncated subtraction and comparisons, jumps and halt each cost one. Each indirect load, store or input-cell read costs one; operand-register access is included in its arithmetic instruction. No floor, real-to-integer conversion, logarithm, Poisson, heap or whole-DP instruction is available. Loops, coefficient generation and heap operations must be implemented and charged. Poisson probabilities are generated from exp by arithmetic, including the mean-zero case. The query receives the stored memory without copying it. Definitions specify computation and encodings; both successful execution and the time bounds are conclusions. The program witnesses and cost proofs remain to be supplied by solvers.
--
--   This formalizes the full headline deterministic bicriteria claim, including nonnegative inputs, compact all-target output and deterministic path retrieval, rather than only inner feasibility or nonconstructive path existence.
--
--   Differences from the source:
--   - reading: infinite-precision real-RAM computation, with exact Poisson probabilities and generating functions → the explicitly listed exact field, comparison, exp, register, memory and control instructions, each costing one; reason: exact exp evaluation is required by the paper computation; no floor, real-to-integer conversion, log or algorithm oracle is provided
--   - encoding: O-tilde(m log(nW)/epsilon^9), suppressing exactly one log n → one positive absolute coefficient outside all instances and epsilon multiplying max(1,m)*(1+log(max(2,n)))*(1+log(max(2,n)*W))/epsilon^9; reason: this is the stated asymptotic bound with totalized empty-edge and small-graph cases, without an instance-dependent coefficient
--   - encoding: nonnegative resources with minor zero-weight bookkeeping → nonnegative real resources, explicit zero-length and zero-budget shortest-tree branches, W=1 when no length is positive, and self-loops ignored in computations; reason: all headline instances remain present; zero optima require zero output length and no division by a zero threshold
--   - encoding: rescale epsilon by a constant, q=Theta(epsilon^-2), and normalized powers of 1+epsilon → delta=epsilon/4, q=ceil(512/delta^2), acceptance 1/4, both potential coefficients 1/8, and guesses a*(1+delta)^r through the first value at least n*b; reason: the explicit choices meet the tail and potential inequalities and preserve the exponent nine and both final factors 1+epsilon
--   - encoding: compact single-source distances and deterministic witness retrieval from the retained tables → sparse memory encoding of the actual tables and boundary trees, a certified upper distance (1+delta)*L from the selected table, and a fixed query program with charged output-sensitive cost (q+1)^2*(path length+1); reason: implicit isolated targets avoid an uncharged linear-in-n initialization and explicit path writing is charged separately from preprocessing
--   - encoding: approximation relative to an exactly budget-feasible optimum → the reported upper distance is at most (1+epsilon) times every exactly feasible comparator path length, with a returned path below that distance; reason: finite nonnegative graph optima are attained by cycle deletion; this formulation also handles zero optima and empty feasible sets without real-infimum defaults
--   - encoding: deterministic choices left unspecified in the routines → first-minimum queue and pair ties, length on tick ties, a fixed edge-list input ABI and a fixed sparse output ABI; reason: these choices specify a single uniform computation and change no allowed instance or guarantee
-- source:
--   Vikrant Ashvinkumar, STOC 2027 submission #289 (October 2026), p.3, Theorem 1 and following paragraph; Definition 1.1 p.2; proof pp.6–12 and 14

import Definitions.Def_NearLinearRSP_TwoResources_RAM

set_option autoImplicit false

namespace NearLinearRSP.TwoResources

theorem deterministic_bicriteria_rsp :
    ∃ preprocessing retrieval : Program, ∃ K : ℝ, 0 < K ∧
      ∀ (I : Instance) (ε : ℝ), 0 < ε → ε < 1 →
        ∃ (steps : ℕ) (snapshot : RAMState),
          Execution preprocessing (encodeInput I ε) initialState snapshot steps ∧
          (steps : ℝ) ≤ K * preprocessingScale I ε ∧ EncodesOutput I ε snapshot ∧
          ∀ t : ℕ, t < I.graph.n →
            readDistance snapshot t = answerDistance I ε t ∧
            (∃ (querySteps : ℕ) (out : RAMState),
              Execution retrieval (encodeInput I ε) (queryStart snapshot t) out querySteps ∧
              queryPath out = answerPath I ε t ∧
              (querySteps : ℝ) ≤ K * retrievalScale ε (answerPath I ε t)) ∧
            (∀ d : ℝ, readDistance snapshot t = some d →
              ∃ P : List ℕ, answerPath I ε t = some P ∧
                IsPath I.graph I.source t P ∧ pathWeight I.length P ≤ d ∧
                pathWeight I.cost P ≤ (1 + ε) * I.budget ∧
                ∀ R : List ℕ, Feasible I t R → d ≤ (1 + ε) * pathWeight I.length R) ∧
            ((∃ R : List ℕ, Feasible I t R) → (readDistance snapshot t).isSome = true) ∧
            (∀ P : List ℕ, answerPath I ε t = some P →
              IsPath I.graph I.source t P ∧ pathWeight I.cost P ≤ (1 + ε) * I.budget) := by sorry

end NearLinearRSP.TwoResources
