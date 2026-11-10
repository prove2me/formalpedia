-- Prove2me | Theorems.Thm_GreedyColoringLCA969_LowerBound_lemma_3_4
-- name    : GreedyColoringLCA969.LowerBound.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T09:49:40.890203+00:00
-- url     : https://prove2.me/theorems/d4887634-56da-44a0-ae79-d8ec162f0767
-- title:
--   Lemma 3.4 — efficiency and success reduction, including the error-free clause
-- statement:
--   Let $\mu$ be any probability law on finite represented graphs, and fix $\widehat R\in\operatorname{supp}(\mu)$. Let $Q,\varepsilon>0$. Both assertions below hold for either the standard graph oracle or the stronger full-list oracle, with that interface fixed throughout.
--
--   1. For $0<\eta<\delta\le1$, put $Q'=3Q/\eta$. If every deterministic LCA that is $(Q',\varepsilon/2)$-efficient on $\widehat R$ has distributional global success strictly less than $\delta-\eta$, every randomized LCA that is $(Q,\varepsilon)$-efficient on $\widehat R$ has global success strictly less than $\delta$ on some $R\in\operatorname{supp}(\mu)$:
--
--   $$\left[\forall B,\ \operatorname{Eff}_{\widehat R}(B,3Q/\eta,\varepsilon/2)\Rightarrow
--   \Pr_{R\sim\mu}[B\text{ succeeds on }R]<\delta-\eta\right]
--   \Rightarrow\left[\forall A,\ \operatorname{Eff}_{\widehat R}(A,Q,\varepsilon)\Rightarrow
--   \exists R\in\operatorname{supp}(\mu),\ \Pr_r[A\text{ succeeds on }R]<\delta\right].$$
--
--   2. For $\delta=1$ and $\eta=0$, the identical implication holds with $Q'=3Q$ and deterministic success strictly less than $1$.
--
--   This reduction keeps the efficiency fraction and success guarantee together. The second clause is independent of the division formula and does not evaluate $Q/0$. The input law may have countably infinite support and may mix graph sizes. A deterministic LCA is an operational rule with its shared tape fixed before the graph is sampled.
--
--   Differences from the source:
--   - encoding: vertex identifiers [n] and positive integer colors → Fin n with zero-based identifiers and positive-integer color type; reason: adding one is a bijection on vertex identifiers; colors remain exactly positive integers
--   - generalization: algorithms that output positive integer labels using finite observable operations → arbitrary next-action rules, also admitting partial or noncomputable runs; reason: every source algorithm embeds by its successive actions; nontermination is failure with infinite cost, and no new graph information is available
--   - encoding: expectations of the number of graph queries and global success probabilities → nonnegative extended query costs integrated against the independent fair-bit product law; reason: finite costs agree exactly; divergent expectations remain infinite, and all cost and success events are measurable
--   - encoding: a graph distribution and its support → a probability measure on the countable discrete space of represented inputs, with positive singleton mass defining support; reason: all finite graphs, all adjacency-list permutations, all sizes, and all probability laws on them are included
--   - encoding: deterministic LCAs and the two reduction clauses → fixed rule/tape pairs, with the two complete clauses conjoined in one theorem; reason: this is precisely seed fixing in Appendix A.2; no randomized expectation is used for deterministic efficiency
--   - generalization: the standard interface of Definition 2.5 and the full-list strengthening used throughout Section 3 → one reduction theorem parameterized by either interface; reason: the oracle response depends only on the input and request; both source interfaces specialize directly
-- source:
--   Zi Song Yeoh, Krzysztof Onak, Dragos-Florian Ristache, STOC 2027 submission #969 (October 2026), Lemma 3.4, p.11 (PDF 12); Appendix A.2, pp.36–37 (PDF 37–38); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/969.pdf

import Definitions.Def_GreedyColoringLCA969_LowerBound_Distribution

open scoped ENNReal
open MeasureTheory
open Classical

namespace GreedyColoringLCA969.LowerBound

/-- Lemma 3.4, printed p.11 / PDF 12 and Appendix A.2, including its eta=0 clause.
Both oracle interfaces use precisely the same execution and seed-fixing semantics. -/
theorem lemma_3_4 (m : OracleMode) (μ : MeasureTheory.Measure Input)
    [MeasureTheory.IsProbabilityMeasure μ] (Rhat : Input) (hhat : InSupport μ Rhat)
    (Q ε : ℝ) (hQ : 0 < Q) (hε : 0 < ε) :
    (∀ η δ : ℝ, 0 < η → η < δ → δ ≤ 1 →
      (∀ B : DeterministicLCA m,
        DeterministicEfficient B Rhat.2 (3 * Q / η) (ε / 2) →
          distributionalSuccess B μ < ENNReal.ofReal (δ - η)) →
      ∀ A : Algorithm m, Efficient A Rhat.2 Q ε →
        ∃ R : Input, InSupport μ R ∧ successProbability A R.2 < ENNReal.ofReal δ) ∧
    ((∀ B : DeterministicLCA m,
        DeterministicEfficient B Rhat.2 (3 * Q) (ε / 2) →
          distributionalSuccess B μ < 1) →
      ∀ A : Algorithm m, Efficient A Rhat.2 Q ε →
        ∃ R : Input, InSupport μ R ∧ successProbability A R.2 < 1) := by sorry

end GreedyColoringLCA969.LowerBound
