-- Prove2me | Theorems.Thm_MaxCompForest_Supplement_theorem_5_3
-- name    : MaxCompForest.Supplement.theorem_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:28:27.988205+00:00
-- url     : https://prove2.me/theorems/8dfc53d1-7605-43fd-8b2e-d8256e5a3ee0
-- title:
--   Theorem 5.3 — partition averages at a spectral budget: $O(\log(q^*+1))$, connected blocks on $K_h$-minor-free graphs, and the matching lower bound
-- statement:
--   Let $G$ be a connected graph on $n\ge2$ vertices with positive conductances, degrees $d_v$, $D=\mathrm{diag}(d_v)$, Laplacian $L$, and eigenvalues $0=\lambda_1<\lambda_2\le\dots\le\lambda_n$ of $N=D^{-1/2}LD^{-1/2}$. Observe $Y=f+\xi$ with $\xi\sim N(0,\sigma^2D^{-1})$, $\sigma>0$, measure error in $\|g\|_D^2=\sum_vd_vg_v^2$, and let $H_R=\{f:f^{\top}Lf\le R^2\}$ and $R^*$ the minimax risk over $H_R$ among all measurable, possibly randomized, estimators. For a partition $Q$, $P_Q$ takes degree-weighted block means and $S_Q=D(I-P_Q)$; a partition law is chosen independently of the signal and the observations. Let $q^*$ be the largest $j$ with $j\sigma^2\le R^2/\lambda_j$ ($j=1$ admitted). There are absolute constants $C,C',c>0$ such that:
--
--   1. for $R>0$ there is a partition law with at most $\min(n,2q^*)$ blocks whose block-average estimator has worst-case risk at most $C\log(q^*+1)R^*$;
--   2. on graphs excluding $K_h$ as a minor, $h\ge3$, at most $\min(n,2q^*)$ connected blocks suffice with factor $C'\log^2h$;
--   3. there are graph families, with $q^*$ arbitrarily large, for which every independent partition law followed by block averaging, even with up to $q^{*2}$ blocks, has worst-case risk at least $c\log(q^*+1)R^*$;
--   4. for $R=0$, one block suffices with risk $\sigma^2$.
--
--   **Formalization Note** "Graph families" is: for every $N_0$ some connected graph and $\sigma,R>0$ with $q^*\ge N_0$. Connected blocks induce connected subgraphs; minor exclusion is for the underlying simple graph.
--
--   Differences from the source:
--   - encoding: a connected positive-conductance graph → a connected loopless WGraph, parallel labelled edges allowed; reason: parallel conductances can equivalently be aggregated (p.7), so a multigraph is the same instance as its aggregated graph; minors and connected blocks use the underlying simple graph
--   - encoding: partition laws, E_µ S_Q ⪯ X → probability mass functions on Mathlib Finpartitions of V; (X − E_µ S_Q).PosSemidef; reason: the set of partitions is finite
--   - encoding: risks and R* → values in ℝ≥0∞; estimators are Markov kernels from observations to estimates; the risk of P_Q Y with Q ∼ µ independent of Y is the expectation under the product of µ and the noise law; reason: measurable, independently randomized estimators are exactly Markov kernels; ℝ≥0∞ represents a possibly infinite supremum without a junk value
--   - encoding: graphs on arbitrary finite vertex and edge sets → vertex and edge types in Type with Fintype and DecidableEq; reason: every finite graph is isomorphic to one on such types
--   - encoding: C, C log² h, Ω(log(q*+1)) → one absolute constant per clause, existentially quantified before every graph, h, σ, R; reason: the constants are absolute
--   - reading: log² h → (log h)², natural logarithm; reason: p.30: O((1 + log h)²) = O(log² h) for h ≥ 3
--   - reading: "There are graph families for which …" → ∃ c > 0, ∀ N₀, ∃ connected graph with n ≥ 2 and σ, R > 0 with q* ≥ N₀ such that every law with at most q*² blocks per draw has worst-case risk ≥ c log(q*+1) R*; reason: an asymptotic lower bound requires q* unbounded along the family (Theorem K.2 supplies it)
--   - reading: "For R = 0, one block suffices with risk σ²" → for every partition with exactly one block, the supremum over H_0 of its risk equals σ²; reason: as in Theorem 5.2
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), Theorem 5.3, p.30 (PDF p.32); setting of §5, p.28 (PDF p.30)

import Mathlib
import Definitions.Def_EffResSparsify_ResistanceSketch_Graph
import Definitions.Def_MaxCompForest_deg
import Definitions.Def_MaxCompForest_lam
import Definitions.Def_MaxCompForest_fnEnergy
import Definitions.Def_MaxCompForest_Supplement_blockRisk
import Definitions.Def_MaxCompForest_Supplement_minimaxRisk
import Definitions.Def_MaxCompForest_Supplement_qStar
import Definitions.Def_MaxCompForest_Supplement_IsConnPartition
import Definitions.Def_MaxCompForest_Supplement_ExcludesCliqueMinor
open EffResSparsify.ResistanceSketch
set_option autoImplicit false

namespace MaxCompForest.Supplement

/-- **Theorem 5.3 (Partition averages at a spectral budget).** In the model of §5:

* for `R > 0` some signal-independent partition law with at most `min(n, 2q*)` blocks has block-average worst-case risk
  at most `C log(q*+1) R*`;
* on graphs excluding `K_h` as a minor, `h ≥ 3`, at most `min(n, 2q*)` connected blocks suffice with factor `C log² h`;
* there are graph families (with `q*` arbitrarily large) for which every independent partition law followed by block
  averaging has worst-case risk `Ω(log(q*+1)) R*`, even if up to `q*²` blocks are allowed;
* for `R = 0`, one block suffices with risk `σ²`.

Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), Theorem 5.3, p.30; the setting of §5, p.28.

**Formalization Note.** Each `O`/`Ω` is one absolute constant chosen before every graph, `h`, `σ`, `R`. `log² h` is
`(log h)²` with the natural logarithm (p.30: `O((1+log h)²) = O(log² h)` for `h ≥ 3`). "Graph families" is: for every
`N₀` some connected graph with `n ≥ 2` and parameters `σ, R > 0` with `q* ≥ N₀`. Minor exclusion is for the
underlying simple graph; a connected block induces a connected subgraph of `G`. -/
theorem theorem_5_3 :
    (∃ C : ℝ, 0 < C ∧
      ∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : WGraph V E), G.IsConnected → 2 ≤ Fintype.card V →
        ∀ (σ R : ℝ), 0 < σ → 0 < R →
          ∃ μ : PMF (Finpartition (Finset.univ : Finset V)),
            (∀ Q ∈ μ.support, Q.parts.card ≤ min (Fintype.card V) (2 * qStar G σ R)) ∧
            (⨆ f : V → ℝ, ⨆ _ : MaxCompForest.fnEnergy G f ≤ R ^ 2, blockRisk G σ μ f) ≤
              ENNReal.ofReal (C * Real.log ((qStar G σ R : ℝ) + 1)) * minimaxRisk G σ R) ∧
    (∃ C : ℝ, 0 < C ∧
      ∀ (h : ℕ), 3 ≤ h →
      ∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : WGraph V E), G.IsConnected → 2 ≤ Fintype.card V →
        ExcludesCliqueMinor G.toSimpleGraph h →
        ∀ (σ R : ℝ), 0 < σ → 0 < R →
          ∃ μ : PMF (Finpartition (Finset.univ : Finset V)),
            (∀ Q ∈ μ.support, Q.parts.card ≤ min (Fintype.card V) (2 * qStar G σ R) ∧
              IsConnPartition G Q) ∧
            (⨆ f : V → ℝ, ⨆ _ : MaxCompForest.fnEnergy G f ≤ R ^ 2, blockRisk G σ μ f) ≤
              ENNReal.ofReal (C * Real.log (h : ℝ) ^ 2) * minimaxRisk G σ R) ∧
    (∃ c : ℝ, 0 < c ∧
      ∀ N₀ : ℕ, ∃ (V E : Type) (_ : Fintype V) (_ : DecidableEq V) (_ : Fintype E) (_ : DecidableEq E)
        (G : WGraph V E) (σ R : ℝ), G.IsConnected ∧ 2 ≤ Fintype.card V ∧ 0 < σ ∧ 0 < R ∧
          N₀ ≤ qStar G σ R ∧
          ∀ μ : PMF (Finpartition (Finset.univ : Finset V)),
            (∀ Q ∈ μ.support, Q.parts.card ≤ qStar G σ R ^ 2) →
            ENNReal.ofReal (c * Real.log ((qStar G σ R : ℝ) + 1)) * minimaxRisk G σ R ≤
              ⨆ f : V → ℝ, ⨆ _ : MaxCompForest.fnEnergy G f ≤ R ^ 2, blockRisk G σ μ f) ∧
    (∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : WGraph V E), G.IsConnected → 2 ≤ Fintype.card V →
      ∀ (σ : ℝ), 0 < σ → ∀ Q : Finpartition (Finset.univ : Finset V), Q.parts.card = 1 →
        (⨆ f : V → ℝ, ⨆ _ : MaxCompForest.fnEnergy G f ≤ (0 : ℝ) ^ 2, blockRisk G σ (PMF.pure Q) f) =
          ENNReal.ofReal (σ ^ 2)) := by sorry

end MaxCompForest.Supplement
