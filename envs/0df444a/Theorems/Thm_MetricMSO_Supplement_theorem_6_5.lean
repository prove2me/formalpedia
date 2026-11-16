-- Prove2me | Theorems.Thm_MetricMSO_Supplement_theorem_6_5
-- name    : MetricMSO.Supplement.theorem_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:05:22.589132+00:00
-- url     : https://prove2.me/theorems/eefd49f7-3e82-4849-8b17-3f049118e48c
-- title:
--   Theorem 6.5 — Nearest-Set Optimization is FPT by $\mathrm{ctw}(G)$, also with a condition $\psi(S)$
-- statement:
--   Consider Nearest-Set Optimization: a connected nonempty unweighted graph $G$, candidates $F\subseteq V(G)$, rational opening costs $o_s$, cost tables $h_v:\{0,\dots,n-1\}\to\mathbb Q\cup\{+\infty\}$ and an optional constraint $|S|=p$ or $|S|\le p$; feasible sets are the nonempty $S\subseteq F$ with only finite costs $h_v(d_G(v,S))$, and the objective is $\sum_{s\in S}o_s+\sum_v h_v(d_G(v,S))$.
--
--   For every fixed representation of the tables from which all entries can be computed in time polynomial in the input length (explicit tables included) there are a computable $f$ and a constant $c$ such that
--
--   1. the minimization variant, the maximization variant, and exact counting of feasible sets and of optimum sets are solved in time $f(\mathrm{ctw}(G))\cdot N^{c}$;
--   2. with an additional condition $\psi(S)\in\mathrm{CMSO}_2[\mathrm{SP},\mathrm{EqGC}]$ given with the input, the same tasks are solved in time $f(|\psi|+\mathrm{ctw}(G))\cdot N^{c}$, with one exponent for all $\psi$.
--
--   Differences from the source:
--   - encoding: N^{O(1)}, machine model unspecified → ∃ c, time f(·)·(N+1)^c for a Mathlib TM2 machine (published HMBinPacking.OutputsWithin), N the length of the binary input; reason: the published goal's conventions; polynomial overhead between machine models
--   - encoding: any fixed representation from which all table entries can be computed in time polynomial in the input length → ∀ machine E and exponent k computing every entry h_v(d), d < n, from the description τ within (N+1)^k steps; reason: explicit tables are one such representation; the statement covers all of them
--   - encoding: ψ(S) a CMSO2[SP, EqGC] condition on G → ψ with one free vertex-set variable, evaluated on G without input predicates; reason: the problem has no input predicates
-- source:
--   Chakraborty, Ordyniak, Siebertz, Model Checking for Metric Extensions of MSO (arXiv:2610.41974, sha256 ad3c5863…), Theorem 6.5, p.42 (PDF 44)

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_MetricMSO_ctw
import Definitions.Def_MetricMSO_IsFormulaIn
import Definitions.Def_MetricMSO_Supplement_NSO

open HMBinPacking (OutputsWithin)

namespace MetricMSO.Supplement

open MetricMSO

/-- **Theorem 6.5.** Chakraborty, Ordyniak, Siebertz (arXiv:2610.41974, sha256 prefix ad3c5863),
p.42 (PDF 44): "We can solve Nearest-Set Optimization, its maximization variant, and exact counting
of feasible or optimum sets in fixed-parameter time with parameter ctw(G). We may also impose a
CMSO2[SP, EqGC] condition ψ(S), with running time f(|ψ| + ctw(G))N^{O(1)} for a computable function
f."

For every fixed representation of the cost tables computable in polynomial time (a machine `E` and
an exponent `k`: `E` computes every entry `h_v(d)`, `d < n`, from the description `τ` within
`(N + 1)^k` steps; explicit tables are one instance) there are a computable `f` and an exponent `c`
such that, for the tasks minimize, maximize, count feasible sets, count minimum sets and count
maximum sets, on connected nonempty graphs:
1. without a condition, one machine answers within `f(ctw(G))·(N + 1)^c` steps;
2. with a condition `ψ(S)` of CMSO2[SP, EqGC] with one free vertex-set variable, given as part of
   the input, one machine answers within `f(|ψ| + ctw(G))·(N + 1)^c` steps (one exponent for all
   `ψ`).

Opening costs and finite table entries are rationals in binary; `+∞` is a forbidden distance; the
optional constraint `|S| = p` or `|S| ≤ p` has `p` in binary.

**Formalization Note** The feasibility decision (`Task.decide`) is not among the tasks of the page
and is excluded. `N` is the length of `nsoInput` (task, graph, `F`, opening costs, `τ`, the
cardinality constraint, the condition). -/
theorem theorem_6_5 :
    ∀ (E : Turing.TM2ComputableAux Bool Bool) (k : ℕ),
      ∃ f : ℕ → ℕ, Computable f ∧ ∃ c : ℕ, ∀ task : Task, task ≠ Task.decide →
        (∃ M : Turing.TM2ComputableAux Bool Bool,
          ∀ J : NSOInstance, J.G.Connected → Represents E k J (nsoInput task J none).length →
            ∃ out, NSOCorrect task J none out ∧
              OutputsWithin M (nsoInput task J none) out
                (f (ctw J.G) * ((nsoInput task J none).length + 1) ^ c)) ∧
        (∃ M : Turing.TM2ComputableAux Bool Bool,
          ∀ (J : NSOInstance) (ψ : Formula), J.G.Connected → ψ.scopedAt 0 0 1 0 = true →
            Represents E k J (nsoInput task J (some ψ)).length →
            ∃ out, NSOCorrect task J (some ψ) out ∧
              OutputsWithin M (nsoInput task J (some ψ)) out
                (f (ψ.length + ctw J.G) * ((nsoInput task J (some ψ)).length + 1) ^ c)) := by sorry

end MetricMSO.Supplement
