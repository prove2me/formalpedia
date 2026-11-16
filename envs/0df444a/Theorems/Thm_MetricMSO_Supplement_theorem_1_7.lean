-- Prove2me | Theorems.Thm_MetricMSO_Supplement_theorem_1_7
-- name    : MetricMSO.Supplement.theorem_1_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:00:37.329126+00:00
-- url     : https://prove2.me/theorems/f1f689cb-8e67-418a-8c87-4b126c102e8a
-- title:
--   Theorem 1.7 — every fixed packing-covering template is FPT by $\mathrm{ctw}(G)$
-- statement:
--   Let $\Phi(\bar X;\bar\delta,\bar\rho)=\psi(\bar X)\wedge\bigwedge_a\mathrm{Sep}_{\delta_a}(X_{i_a},X_{j_a})\wedge\bigwedge_b\mathrm{Cover}_{\rho_b}(U_b,X_{\ell_b})$ be a fixed packing-covering template with side formula $\psi\in\mathrm{CMSO}_2[\mathrm{SP},\mathrm{EqGC}]$. There are a computable function $f_\Phi$ and a constant $c_\Phi$ such that each of the following tasks is solved by one algorithm in time
--
--   $$f_\Phi(\mathrm{ctw}(G))\cdot N^{c_\Phi}$$
--
--   on every graph $G$ with input predicates and every valuation of the numerical symbols by nonnegative integers at most $n$ given in binary, where $N$ is the total binary input length (graph, predicates, template, threshold values, signed binary vertex weights):
--
--   1. decide whether a satisfying assignment exists;
--   2. compute a minimum-weight and a maximum-weight satisfying assignment whenever one exists;
--   3. count all satisfying assignments, the minimum-weight ones and the maximum-weight ones.
--
--   The graph need not be connected. The exponent may depend on $\Phi$ (Theorem 7.18 shows it cannot be made independent of $|\Phi|$ unless FPT = W[1]), and the threshold values are part of the input, not of the parameter. No tree decomposition is given.
--
--   Differences from the source:
--   - encoding: N^{O(1)}, machine model unspecified → ∃ c, time f(·)·(N+1)^c for a Mathlib TM2 machine (published HMBinPacking.OutputsWithin), N the length of the binary input; reason: the published goal's conventions; polynomial overhead between machine models
--   - encoding: distances in Z≥0 ∪ {∞}, valuation η: Δ → Z≥0 → Mathlib edist in ℕ∞; η a list indexed by symbol, atoms with out-of-range indices false; reason: Lean representation; same instances
--   - generalization: instances over a fixed finite unary signature → instances with any number of vertex and edge predicates; predicates not named by Φ are ignored, a target L_j with j ≥ q is ∅; reason: the fixed signature is a special case; extra predicates only lengthen the input
--   - generalization: ψ(X1, …, Xp) with exactly the displayed free variables → free variables of ψ among X1, …, Xp; reason: a set used only in metric atoms is allowed; the paper's templates are a special case
-- source:
--   Chakraborty, Ordyniak, Siebertz, Model Checking for Metric Extensions of MSO (arXiv:2610.41974, sha256 ad3c5863…), Theorem 1.7, p.7 (PDF 9), restated p.30 (PDF 32); threshold bound p.8 (PDF 10)

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_MetricMSO_ctw
import Definitions.Def_MetricMSO_Supplement_CorrectAnswerOn
import Definitions.Def_MetricMSO_Supplement_Template

open HMBinPacking (OutputsWithin)

namespace MetricMSO.Supplement

open MetricMSO

/-- **Theorem 1.7.** Chakraborty, Ordyniak, Siebertz (arXiv:2610.41974, sha256 prefix ad3c5863),
p.7 (PDF 9), restated p.30 (PDF 32): "For every fixed packing-covering template Φ, we can decide
whether a satisfying assignment exists, compute a minimum-weight or maximum-weight satisfying
assignment whenever one exists, and count all satisfying assignments or all optimum assignments
exactly in time f_Φ(ctw(G))N^{O_Φ(1)}, for a computable function f_Φ."

For every well-formed template `Φ` there are a computable `f_Φ` and an exponent `c_Φ` such that for
each of the six tasks one machine `M` (fixed with `Φ`, before the instance) reads the input
(`templateInput`: task, instance, template, binary threshold values, and the signed binary vertex
weights for the weighted tasks; no decomposition) and writes a correct answer within
`f_Φ(ctw(G))·(N + 1)^{c_Φ}` steps, for every instance and every valuation whose values are at most
`n` ("We assume here (and below) that all numerical distance thresholds are bounded by n", p.8).

**Formalization Note** The exponent depends on `Φ` (`∃ c` after `∀ Φ`); the threshold values are
inputs, not parameters. The graph need not be connected. -/
theorem theorem_1_7 :
    ∀ T : Template, T.WellFormed →
      ∃ f : ℕ → ℕ, Computable f ∧ ∃ c : ℕ, ∀ task : Task,
        ∃ M : Turing.TM2ComputableAux Bool Bool,
          ∀ (I : Instance) (η : List ℕ) (w : Weights I T.p 0), (∀ d ∈ η, d ≤ I.n) →
            ∃ out, CorrectAnswerOn task (T.Sol I η) w out ∧
              OutputsWithin M (templateInput task I T η w) out
                (f (ctw I.G) * ((templateInput task I T η w).length + 1) ^ c) := by sorry

end MetricMSO.Supplement
