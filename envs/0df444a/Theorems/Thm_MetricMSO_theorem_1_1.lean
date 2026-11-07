-- Prove2me | Theorems.Thm_MetricMSO_theorem_1_1
-- name    : MetricMSO.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:46:21.42822+00:00
-- url     : https://prove2.me/theorems/7180149c-7ebc-4566-b836-07c182a6c250
-- title:
--   Theorem 1.1 — model checking, optimization and counting for $\mathrm{CMSO}[\mathsf{SP},\mathsf{EqGC}]$ are FPT by $\mathrm{ctw}$ and by $\mathrm{gcw}$
-- statement:
--   For the logics below, one can perform model checking, decide whether a satisfying assignment to the free monadic variables exists, compute an assignment minimizing or maximizing an additive weight objective with signed binary weights, and count the satisfying assignments or the optimum assignments. There are a computable function $f$ and a constant $c$ such that, with $N$ the total binary input length:
--
--   1. for $\varphi\in\mathrm{CMSO}_2[\mathsf{SP},\mathsf{EqGC}]$ these problems are solved in time
--   $$f(|\varphi|+\mathrm{ctw}(G))N^{c}\quad\text{and also in time}\quad f(|\varphi|+\mathrm{tw}(G)+\mathrm{cbl}(G))N^{c};$$
--   2. for $\varphi\in\mathrm{CMSO}_1[\mathsf{SP},\mathsf{EqGC}]$ these problems are solved in time
--   $$f(|\varphi|+\mathrm{gcw}(G))N^{c},\qquad\mathrm{gcw}(G)=\mathrm{cw}(G)+\mathrm{cbl}(G).$$
--
--   The graph, the input predicates, the formula and the weights are the whole input: no tree decomposition or cliquewidth expression is given.
--
--   This is the first main result of the paper. It lifts Courcelle's theorem to metric atoms on bag-connected treewidth and geodesic cliquewidth.
--
--   **Formalization Note** One $f$ and one $c$ serve every task and both parts. For each task and each part one machine is fixed before the graph and the formula, so the statement is fixed-parameter tractability, not XP. Model checking is the deciding task with no free variables.
--
--   Differences from the source:
--   - reading: "For a computable function f" and N^{O(1)}, over several problems and logics → one f and one c for all six tasks and both parts, and one machine per task and part fixed before the graph and the formula; reason: the strongest reading, and the one of Theorem 2.8; finitely many tasks and parts combine by taking maxima
--   - reading: "or equivalently by |φ| + tw(G) + cbl(G)" → the same machine run meets both bounds of part (i); reason: a statement of both parameters needs no inequality (2), and it is at least as strong as either alone
--   - generalization: formulas with valid atoms: 0 ≤ a < ℓ, ℓ ≥ 2, indices of existing input predicates → also formulas with an atom outside these ranges, which reads as false; reason: such an atom is checkable from the input and can be replaced by falsity, and the source formulas are the special case
--   - encoding: the running time of an unspecified algorithm, including arithmetic and writing the output → the published OutputsWithin: a Mathlib multi-stack Turing machine (TM2) halting with the output within t steps; reason: time classes f(k)N^{O(1)} are closed under polynomial simulation, so the machine model does not change the statement
--   - encoding: N^{O(1)} (resp. N^c) → (N+1)^c with c a natural number; reason: N ≥ 1 for every machine input, and the classes coincide
--   - encoding: the instance as binary input of length N; answers as stated in Definitions 2.6 and 2.7 → the codes encodeInput and CorrectAnswer; reason: any two standard encodings have polynomially related lengths; the input holds no decomposition or width
--   - encoding: φ(X₁,…,X_r) with free set variables in any order → IsFormulaIn φ rV rE with vertex-set variables listed before edge-set variables; reason: a renaming; no instance changes
--   - encoding: tw, ctw, cw as minima, −1 on the graph with no vertex → sInf on ℕ, with 0 on the graph with no vertex; reason: the bounds at n = 0 are unaffected
-- source:
--   Chakraborty, Ordyniak, Siebertz, Model Checking for Metric Extensions of MSO (arXiv:2610.41974, sha256 ad3c586330b037548a2b4a977081284996698f39c1b55c17b91cb81a536d3dd9), Theorem 1.1, p.4 (PDF 6), restated p.29 (PDF 31)

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_MetricMSO_encodeInput
import Definitions.Def_MetricMSO_IsCMSO1
import Definitions.Def_MetricMSO_IsFormulaIn
import Definitions.Def_MetricMSO_cbl
import Definitions.Def_MetricMSO_ctw
import Definitions.Def_PlantedSubgraphLD_tw
import Definitions.Def_MetricMSO_gcw

open HMBinPacking (OutputsWithin)
open PlantedSubgraphLD (tw)

namespace MetricMSO

/-- **Theorem 1.1.** Chakraborty, Ordyniak, Siebertz (arXiv:2610.41974, sha256 prefix ad3c5863), p.4 (PDF 6), restated p.29 (PDF 31): "For
each of the following logics, we can perform model checking, decide whether a satisfying assignment to
the free monadic variables exists, compute an assignment minimizing or maximizing an additive weight
objective, and count the satisfying assignments or the optimum assignments. For a computable function
f, we obtain the following running times. (i) For φ ∈ CMSO2[SP, EqGC], we can solve these problems in
time f(|φ| + ctw(G))N^{O(1)}. Thus these problems are fixed-parameter tractable parameterized by
|φ| + ctw(G), or equivalently by |φ| + tw(G) + cbl(G). (ii) For φ ∈ CMSO1[SP, EqGC], we can solve these
problems in time f(|φ| + gcw(G))N^{O(1)}. Thus these problems are fixed-parameter tractable
parameterized by |φ| + gcw(G) = |φ| + cw(G) + cbl(G)."

**Formalization Note** One `f` and one exponent `c` serve every task and both parts; for each task and
part one machine `M` is fixed before the graph and the formula. The machine reads `encodeInput`, of
length `N`: the task, the graph, the input predicates, the formula, the numbers of free set variables and
(for weighted tasks) the signed binary weights, with no decomposition or expression (p.29). Model
checking is `Task.decide` with `rV = rE = 0`. Part (i) carries both parameters of the page's "or
equivalently". `gcw(G) = cw(G) + cbl(G)` is definitional. -/
theorem theorem_1_1 :
    ∃ f : ℕ → ℕ, Computable f ∧ ∃ c : ℕ, ∀ task : Task,
      (∃ M : Turing.TM2ComputableAux Bool Bool,
        ∀ (I : Instance) (rV rE : ℕ) (φ : Formula) (w : Weights I rV rE), IsFormulaIn φ rV rE →
          ∃ out, CorrectAnswer task I φ rV rE w out ∧
            OutputsWithin M (encodeInput task I φ rV rE w) out
              (f (φ.length + ctw I.G) * ((encodeInput task I φ rV rE w).length + 1) ^ c) ∧
            OutputsWithin M (encodeInput task I φ rV rE w) out
              (f (φ.length + tw I.G + cbl I.G) *
                ((encodeInput task I φ rV rE w).length + 1) ^ c)) ∧
      (∃ M : Turing.TM2ComputableAux Bool Bool,
        ∀ (I : Instance) (rV : ℕ) (φ : Formula) (w : Weights I rV 0),
          IsCMSO1 φ → IsFormulaIn φ rV 0 →
          ∃ out, CorrectAnswer task I φ rV 0 w out ∧
            OutputsWithin M (encodeInput task I φ rV 0 w) out
              (f (φ.length + gcw I.G) * ((encodeInput task I φ rV 0 w).length + 1) ^ c)) := by sorry

end MetricMSO
