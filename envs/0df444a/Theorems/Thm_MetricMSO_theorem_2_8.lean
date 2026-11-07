-- Prove2me | Theorems.Thm_MetricMSO_theorem_2_8
-- name    : MetricMSO.theorem_2_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:46:01.414048+00:00
-- url     : https://prove2.me/theorems/5c726a02-079b-4799-9238-01444f9047ba
-- title:
--   Theorem 2.8 — Courcelle's theorem for treewidth
-- statement:
--   There are a computable function $f$ and a constant $c$ such that each of the following tasks can be performed in time $f(|\varphi|+\mathrm{tw}(G))N^c$:
--
--   1. given a graph $G$ and a $\mathrm{CMSO}_2$ sentence $\varphi$, decide whether $G\models\varphi$;
--   2. given a graph $G$, a $\mathrm{CMSO}_2$ formula $\varphi$ whose free variables are vertex-set or edge-set variables, and signed binary weights, compute a minimum-weight or maximum-weight satisfying assignment and its weight, or report that no satisfying assignment exists;
--   3. given a graph $G$ and such a formula, count all satisfying assignments exactly, and when weights and an optimization objective are also given, count all optimum assignments exactly.
--
--   Here $N$ is the total binary input length. No decomposition is part of the input. This is the classical theorem the goal reduces to; it is cited in the paper, not proved there.
--
--   Differences from the source:
--   - generalization: item 1 decides G ⊨ φ for a sentence φ → Task.decide also for formulas with free set variables, the sentence being rV = rE = 0; reason: this is the "or report that no satisfying assignment exists" of item 2, and it specializes to item 1
--   - generalization: formulas with valid atoms: 0 ≤ a < ℓ, ℓ ≥ 2, indices of existing input predicates → also formulas with an atom outside these ranges, which reads as false; reason: such an atom is checkable from the input and can be replaced by falsity, and the source formulas are the special case
--   - encoding: the running time of an unspecified algorithm, including arithmetic and writing the output → the published OutputsWithin: a Mathlib multi-stack Turing machine (TM2) halting with the output within t steps; reason: time classes f(k)N^{O(1)} are closed under polynomial simulation, so the machine model does not change the statement
--   - encoding: N^{O(1)} (resp. N^c) → (N+1)^c with c a natural number; reason: N ≥ 1 for every machine input, and the classes coincide
--   - encoding: the instance as binary input of length N; answers as stated in Definitions 2.6 and 2.7 → the codes encodeInput and CorrectAnswer; reason: any two standard encodings have polynomially related lengths; the input holds no decomposition or width
--   - encoding: φ(X₁,…,X_r) with free set variables in any order → IsFormulaIn φ rV rE with vertex-set variables listed before edge-set variables; reason: a renaming; no instance changes
--   - encoding: tw as a minimum, −1 on the graph with no vertex → sInf on ℕ, with 0 on the graph with no vertex; reason: the bound at n = 0 is unaffected
-- source:
--   Chakraborty, Ordyniak, Siebertz, Model Checking for Metric Extensions of MSO (arXiv:2610.41974, sha256 ad3c586330b037548a2b4a977081284996698f39c1b55c17b91cb81a536d3dd9), Theorem 2.8, p.17 (PDF 19)

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_MetricMSO_encodeInput
import Definitions.Def_MetricMSO_IsCMSO1
import Definitions.Def_MetricMSO_IsFormulaIn
import Definitions.Def_MetricMSO_ctw
import Definitions.Def_PlantedSubgraphLD_tw

open HMBinPacking (OutputsWithin)
open PlantedSubgraphLD (tw)

namespace MetricMSO

/-- **Theorem 2.8 (Courcelle's theorem for treewidth).** Chakraborty, Ordyniak, Siebertz (arXiv:2610.41974, sha256 prefix ad3c5863), p.17
(PDF 19): "There are a computable function f and a constant c such that we can perform each of the
following tasks in time f(|φ| + tw(G))N^c. 1. Given a graph G and a CMSO2 sentence φ, we decide whether
G |= φ. 2. Given a graph G, a CMSO2 formula φ whose free variables are vertex-set or edge-set variables,
and signed binary weights, we compute a minimum-weight or maximum-weight satisfying assignment and its
weight, or report that no satisfying assignment exists. 3. Given a graph G and a CMSO2 formula φ whose
free variables are vertex-set or edge-set variables, we count all satisfying assignments exactly, and
when weights and an optimization objective are also given, we may instead count all optimum assignments
exactly."

**Formalization Note** The six `Task`s are the page's items. `Task.decide` is stated for formulas with
free set variables as well as for sentences (`rV = rE = 0`, item 1): this is the "or report that no
satisfying assignment exists" of item 2. A machine `M` is fixed before the formula and the graph, and
reads the code `encodeInput` of length `N`, with no decomposition. -/
theorem theorem_2_8 :
    ∃ f : ℕ → ℕ, Computable f ∧ ∃ c : ℕ, ∀ task : Task,
      ∃ M : Turing.TM2ComputableAux Bool Bool,
        ∀ (I : Instance) (rV rE : ℕ) (φ : Formula) (w : Weights I rV rE),
          NoMetric φ → IsFormulaIn φ rV rE →
          ∃ out, CorrectAnswer task I φ rV rE w out ∧
            OutputsWithin M (encodeInput task I φ rV rE w) out
              (f (φ.length + tw I.G) * ((encodeInput task I φ rV rE w).length + 1) ^ c) := by sorry

end MetricMSO
