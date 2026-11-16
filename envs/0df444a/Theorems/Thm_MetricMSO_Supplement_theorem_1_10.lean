-- Prove2me | Theorems.Thm_MetricMSO_Supplement_theorem_1_10
-- name    : MetricMSO.Supplement.theorem_1_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:02:18.35829+00:00
-- url     : https://prove2.me/theorems/0a06f46e-e73e-4d6b-a90d-a9ceaf33544c
-- title:
--   Theorem 1.10 — nearest-label formulas are FPT by $|\psi|+q+\mathrm{ctw}(G)$ with a uniform exponent
-- statement:
--   Let the unary input predicates $L_1,\dots,L_q$ partition $V(G)$, and let $\theta(S,\bar X)$ be a single-interface nearest-label formula: a $\mathrm{CMSO}_2[\mathrm{SP},\mathrm{EqGC}]$ formula that may also use atoms $\mathrm{NearLab}_i(v;S)$, all with the same free set $S$, which no quantifier binds. The solutions are the assignments $(S,\bar X)$ of all displayed free sets with $S\ne\emptyset$.
--
--   There are a computable $f$ and a single constant $c$ such that feasibility, minimum- and maximum-weight optimization with signed binary vertex weights, and counting of satisfying and of optimum assignments are each solved by one algorithm in time
--
--   $$f(|\theta|+q+\mathrm{ctw}(G))\cdot N^{c}$$
--
--   for every such formula given as part of the input. The exponent is independent of the formula.
--
--   Differences from the source:
--   - encoding: N^{O(1)}, machine model unspecified → ∃ c, time f(·)·(N+1)^c for a Mathlib TM2 machine (published HMBinPacking.OutputsWithin), N the length of the binary input; reason: the published goal's conventions; polynomial overhead between machine models
--   - encoding: labels L1, …, Lq; distinguished set S → 0-based predicate indices; S the vertex-set variable of level 0; reason: Lean de Bruijn convention
--   - generalization: graphs with unary label predicates → instances may also carry edge predicates; reason: the paper's instances are the case q' = 0; θ may ignore them
--   - encoding: distances in Z≥0 ∪ {∞}, d_G(v, S) a minimum with min ∅ = ∞ → Mathlib edist in ℕ∞, distSet an infimum (⊤ on ∅); atoms with an out-of-range label or variable index false; reason: Lean representation; same instances
--   - generalization: θ(S, X̄) with exactly the displayed free sets → free variables of θ among the vertex-set levels 0, …, r − 1 (S need not occur, but S ≠ ∅ is still required of every solution); reason: the paper's formulas are a special case
-- source:
--   Chakraborty, Ordyniak, Siebertz, Model Checking for Metric Extensions of MSO (arXiv:2610.41974, sha256 ad3c5863…), Theorem 1.10, p.9 (PDF 11), restated p.30 (PDF 32)

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_MetricMSO_ctw
import Definitions.Def_MetricMSO_Supplement_CorrectAnswerOn
import Definitions.Def_MetricMSO_Supplement_NearLab

open HMBinPacking (OutputsWithin)

namespace MetricMSO.Supplement

open MetricMSO

/-- **Theorem 1.10.** Chakraborty, Ordyniak, Siebertz (arXiv:2610.41974, sha256 prefix ad3c5863),
p.9 (PDF 11), restated p.30 (PDF 32): "For a single-interface nearest-label formula ψ(S, X̄), we can
solve feasibility, additive vertex-weight optimization, and exact counting of satisfying or optimum
assignments in time f(|ψ| + q + ctw(G))N^{O(1)}, where f is computable and the polynomial exponent is
independent of the formula."

One computable `f` and one exponent `c` serve every single-interface nearest-label formula; for
each task one machine reads the input (task, instance with its `q` label predicates, the formula,
the number `r` of free sets, the weights for weighted tasks) and, on every instance whose labels
partition `V(G)`, writes a correct answer for the solutions `(S, X̄)` with `S ≠ ∅` within
`f(|ψ| + q + ctw(G))·(N + 1)^c` steps. -/
theorem theorem_1_10 :
    ∃ f : ℕ → ℕ, Computable f ∧ ∃ c : ℕ, ∀ task : Task,
      ∃ M : Turing.TM2ComputableAux Bool Bool,
        ∀ (I : Instance) (θ : XFormula) (r : ℕ) (w : Weights I r 0),
          IsLabelPartition I → IsNearLabFormula θ r →
          ∃ out, CorrectAnswerOn task (NLSol I θ r) w out ∧
            OutputsWithin M (nearLabInput task I θ r w) out
              (f (θ.length + I.q + ctw I.G) *
                ((nearLabInput task I θ r w).length + 1) ^ c) := by sorry

end MetricMSO.Supplement
