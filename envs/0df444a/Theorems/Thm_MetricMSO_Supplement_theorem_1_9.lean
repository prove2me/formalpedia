-- Prove2me | Theorems.Thm_MetricMSO_Supplement_theorem_1_9
-- name    : MetricMSO.Supplement.theorem_1_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:01:47.854209+00:00
-- url     : https://prove2.me/theorems/37f14f37-1e6b-4b6b-84d6-c5bd6c3b27bd
-- title:
--   Theorem 1.9 — one-cover formulas are FPT by $|\Phi|+\mathrm{ctw}(G)$ with a uniform exponent
-- statement:
--   A one-cover formula is $\Phi(\bar X;\rho)=\psi(\bar X)\wedge\mathrm{Cover}_\rho(U,S)$, where $\psi\in\mathrm{CMSO}_2[\mathrm{SP},\mathrm{EqGC}]$, the target $U$ is $V(G)$ or an input predicate, $S$ is one distinguished free set among $\bar X$, and the radius $\rho$ is a numerical symbol whose value is given in binary. The side formula, its free sets and $\rho$ are all part of the input.
--
--   There are a computable $f$ and a single constant $c$ such that feasibility, minimum- and maximum-weight optimization with signed binary vertex weights, and counting of satisfying and of optimum assignments are each solved by one algorithm in time
--
--   $$f(|\Phi|+\mathrm{ctw}(G))\cdot N^{c}$$
--
--   on every graph and every one-cover formula, for radius values at most $n$. Here $|\Phi|$ counts the symbol $\rho$ but not its value, and $N$ is the total binary input length. The exponent is independent of the formula.
--
--   Differences from the source:
--   - encoding: N^{O(1)}, machine model unspecified → ∃ c, time f(·)·(N+1)^c for a Mathlib TM2 machine (published HMBinPacking.OutputsWithin), N the length of the binary input; reason: the published goal's conventions; polynomial overhead between machine models
--   - encoding: distances in Z≥0 ∪ {∞}, valuation η: Δ → Z≥0 → Mathlib edist in ℕ∞; η a list indexed by symbol, atoms with out-of-range indices false; reason: Lean representation; same instances
--   - generalization: instances over a fixed finite unary signature → instances with any number of vertex and edge predicates; predicates not named by Φ are ignored, a target L_j with j ≥ q is ∅; reason: the fixed signature is a special case; extra predicates only lengthen the input
--   - encoding: a one-cover formula ψ(X̄) ∧ Cover_ρ(U, S) → a Template with no separation atom and one covering atom; reason: the same expressions
--   - generalization: ψ(X̄) with exactly the displayed free variables → free variables of ψ among X̄ (Template.WellFormed); reason: a selected set may occur only in the covering atom; the paper's one-cover formulas are a special case
-- source:
--   Chakraborty, Ordyniak, Siebertz, Model Checking for Metric Extensions of MSO (arXiv:2610.41974, sha256 ad3c5863…), Theorem 1.9, p.8 (PDF 10), restated p.30 (PDF 32)

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_MetricMSO_ctw
import Definitions.Def_MetricMSO_Supplement_CorrectAnswerOn
import Definitions.Def_MetricMSO_Supplement_Template

open HMBinPacking (OutputsWithin)

namespace MetricMSO.Supplement

open MetricMSO

/-- **Theorem 1.9.** Chakraborty, Ordyniak, Siebertz (arXiv:2610.41974, sha256 prefix ad3c5863),
p.8 (PDF 10), restated p.30 (PDF 32): "For a one-cover formula, we can solve feasibility, additive
vertex-weight optimization, and exact counting of satisfying or optimum assignments in time
f(|Φ| + ctw(G))N^{O(1)}, where f is computable and the polynomial exponent is independent of the
formula."

One computable `f` and one exponent `c` serve every one-cover formula `Φ = ψ(X̄) ∧ Cover_ρ(U, S)`;
for each task one machine reads the input (task, instance, the formula `Φ`, the binary value of `ρ`,
and the weights for weighted tasks) and writes a correct answer within
`f(|Φ| + ctw(G))·(N + 1)^c` steps. `|Φ|` counts the symbol `ρ`, not its value. Thresholds are at
most `n` (p.8).

**Formalization Note** A one-cover formula is a `Template` with no separation atom and one
covering atom; the side formula, its number of free sets, the target `U` and the distinguished set
`S` are part of the input. -/
theorem theorem_1_9 :
    ∃ f : ℕ → ℕ, Computable f ∧ ∃ c : ℕ, ∀ task : Task,
      ∃ M : Turing.TM2ComputableAux Bool Bool,
        ∀ (I : Instance) (T : Template) (η : List ℕ) (w : Weights I T.p 0),
          T.WellFormed → T.IsOneCover → (∀ d ∈ η, d ≤ I.n) →
          ∃ out, CorrectAnswerOn task (T.Sol I η) w out ∧
            OutputsWithin M (templateInput task I T η w) out
              (f (T.length + ctw I.G) * ((templateInput task I T η w).length + 1) ^ c) := by sorry

end MetricMSO.Supplement
