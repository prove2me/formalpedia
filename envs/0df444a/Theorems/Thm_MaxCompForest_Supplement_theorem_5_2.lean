-- Prove2me | Theorems.Thm_MaxCompForest_Supplement_theorem_5_2
-- name    : MaxCompForest.Supplement.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:27:54.743194+00:00
-- url     : https://prove2.me/theorems/06b8e40f-0536-4ba4-9c9b-c4d85a3363c0
-- title:
--   Theorem 5.2 — minimax approximation by independent block means, (5.5) and (5.6)
-- statement:
--   Let $G$ be a connected graph on $n\ge2$ vertices with positive conductances, degrees $d_v$, $D=\mathrm{diag}(d_v)$, Laplacian $L$, and eigenvalues $0=\lambda_1<\lambda_2\le\dots\le\lambda_n$ of $N=D^{-1/2}LD^{-1/2}$. Observe $Y=f+\xi$ with $\xi\sim N(0,\sigma^2D^{-1})$, $\sigma>0$, measure error in $\|g\|_D^2=\sum_vd_vg_v^2$, and let $H_R=\{f:f^{\top}Lf\le R^2\}$ and $R^*$ the minimax risk over $H_R$ among all measurable, possibly randomized, estimators. For a partition $Q$, $P_Q$ takes degree-weighted block means and $S_Q=D(I-P_Q)$; a partition law is chosen independently of the signal and the observations. Let $q^*$ be the largest $j$ with $j\sigma^2\le R^2/\lambda_j$ ($j=1$ admitted).
--
--   Suppose that for every $1\le q<n$ a signal-independent law $\mu_q$ has at most $b_q\le c_bq$ blocks per draw and
--   $$\mathbb E_{\mu_q}S_Q\preceq\frac{A_q}{\lambda_{q+1}}L .$$
--   Then:
--
--   1. for $Q\sim\mu_q$ independent of $Y$, the estimator $\hat f=P_QY$ satisfies, for every $f\in\mathbb R^V$,
--   $$\mathbb E\|\hat f-f\|_D^2\le\frac{A_q}{\lambda_{q+1}}f^{\top}Lf+\sigma^2b_q;\tag{5.5}$$
--   2. for $R>0$ with $q^*<n$, the law $\mu_{q^*}$ gives
--   $$\sup_{f\in H_R}\mathbb E\|\hat f-f\|_D^2\le(20A_{q^*}+10c_b)R^*;\tag{5.6}$$
--   3. if $q^*=n$, the singleton partition has worst-case risk at most $10R^*$;
--   4. if $R=0$, one block has risk $\sigma^2$;
--   5. consequently, by (5.4), there is an absolute $C$ such that for every such $G$, $\sigma$ and $R>0$ some partition law drawn independently of the signal and observations, with at most $\min(n,2q^*)$ blocks per draw, has worst-case risk at most $C\log(q^*+1)R^*$.
--
--   Independent block averaging is therefore within a logarithmic factor of the unrestricted minimax risk.
--
--   **Formalization Note** Clause 4 is stated as an equality for the worst case over $H_0$ and for every partition with one block; clause 5 includes $q^*=n$.
--
--   Differences from the source:
--   - encoding: a connected positive-conductance graph → a connected loopless WGraph, parallel labelled edges allowed; reason: parallel conductances can equivalently be aggregated (p.7), so a multigraph is the same instance as its aggregated graph; minors and connected blocks use the underlying simple graph
--   - encoding: partition laws, E_µ S_Q ⪯ X → probability mass functions on Mathlib Finpartitions of V; (X − E_µ S_Q).PosSemidef; reason: the set of partitions is finite
--   - encoding: risks and R* → values in ℝ≥0∞; estimators are Markov kernels from observations to estimates; the risk of P_Q Y with Q ∼ µ independent of Y is the expectation under the product of µ and the noise law; reason: measurable, independently randomized estimators are exactly Markov kernels; ℝ≥0∞ represents a possibly infinite supremum without a junk value
--   - encoding: graphs on arbitrary finite vertex and edge sets → vertex and edge types in Type with Fintype and DecidableEq; reason: every finite graph is isomorphic to one on such types
--   - reading: "If R = 0, one block has risk σ²" → for every partition with exactly one block, the supremum over H_0 of its risk equals σ²; reason: "has risk σ²" is an equality, and H_0 consists of constants, all with the same risk
--   - reading: "Consequently (5.4) yields an O(log(q*+1)) minimax approximation … with at most min(n, 2q*) blocks and the boundary cases just described" → ∃ absolute C > 0, ∀ G, σ > 0, R > 0, ∃ law with at most min(n, 2q*) blocks per draw and worst-case risk ≤ C log(q*+1) R*; the R = 0 case is clause 4; reason: the constant of (5.4) is absolute
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), Theorem 5.2, p.30 (PDF p.32); setting of §5, p.28 (PDF p.30); (5.4), p.29 (PDF p.31)

import Mathlib
import Definitions.Def_EffResSparsify_ResistanceSketch_Graph
import Definitions.Def_MaxCompForest_deg
import Definitions.Def_MaxCompForest_lam
import Definitions.Def_MaxCompForest_fnEnergy
import Definitions.Def_MaxCompForest_Supplement_expResid
import Definitions.Def_MaxCompForest_Supplement_blockRisk
import Definitions.Def_MaxCompForest_Supplement_minimaxRisk
import Definitions.Def_MaxCompForest_Supplement_qStar
open EffResSparsify.ResistanceSketch
set_option autoImplicit false

namespace MaxCompForest.Supplement

/-- **Theorem 5.2 (Minimax approximation by independent block means).** Let `G` be connected with `n ≥ 2` and positive
conductances, `D` its degree matrix, `Y = f + ξ`, `ξ ∼ N(0, σ²D⁻¹)`, `σ > 0`. Suppose, for every `1 ≤ q < n`, a
signal-independent law `μ_q` has at most `b_q ≤ c_b q` blocks per draw and `E_{μ_q} S_Q ⪯ (A_q/λ_{q+1}) L`. Then:

* (5.5) for `Q ∼ μ_q` independent of `Y`, `f̂ = P_Q Y` has `E‖f̂ − f‖²_D ≤ (A_q/λ_{q+1}) fᵀLf + σ² b_q` for every `f`;
* (5.6) for `R > 0` and `q* < n`, `sup_{f ∈ H_R} E‖f̂ − f‖²_D ≤ (20A_{q*} + 10c_b) R*` under `μ_{q*}`;
* if `q* = n`, the singleton partition has risk at most `10R*`;
* if `R = 0`, one block has risk `σ²`;
* consequently (with (5.4)) there is an absolute `C` such that for `R > 0` some signal-independent law with at most
  `min(n, 2q*)` blocks per draw has worst-case risk at most `C log(q*+1) R*`.

Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), Theorem 5.2, p.30; the setting of §5, p.28 and (5.4), p.29.

**Formalization Note.** Laws are probability mass functions on the partitions of `V`; `E S_Q ⪯ X` is
`(X − E S_Q).PosSemidef`. Risks are in `ℝ≥0∞`; `H_R` is `fᵀ L f ≤ R²` (`fnEnergy`). "Risk" of a fixed law at
`R = 0` and `q* = n` is the worst case over `H_R`; at `R = 0` it is stated as an equality, as printed ("has risk
`σ²`"). "One block" is any partition with one part. In the last clause `q* = n` is included: the law may be the
singleton partition, which has `n ≤ min(n, 2n)` blocks. -/
theorem theorem_5_2 :
    (∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : WGraph V E), G.IsConnected → 2 ≤ Fintype.card V →
      ∀ (σ : ℝ), 0 < σ →
      ∀ (μ : ℕ → PMF (Finpartition (Finset.univ : Finset V))) (A : ℕ → ℝ) (b : ℕ → ℕ) (cb : ℝ),
        (∀ q, 1 ≤ q → q < Fintype.card V →
          (∀ Q ∈ (μ q).support, Q.parts.card ≤ b q) ∧ (b q : ℝ) ≤ cb * q ∧
          ((A q / MaxCompForest.lam G (MaxCompForest.deg G) q) • G.laplacian -
            expResid (MaxCompForest.deg G) (μ q)).PosSemidef) →
        (∀ q, 1 ≤ q → q < Fintype.card V → ∀ f : V → ℝ,
          blockRisk G σ (μ q) f ≤ ENNReal.ofReal
            (A q / MaxCompForest.lam G (MaxCompForest.deg G) q * MaxCompForest.fnEnergy G f + σ ^ 2 * b q)) ∧
        (∀ R : ℝ, 0 < R → qStar G σ R < Fintype.card V →
          (⨆ f : V → ℝ, ⨆ _ : MaxCompForest.fnEnergy G f ≤ R ^ 2, blockRisk G σ (μ (qStar G σ R)) f) ≤
            ENNReal.ofReal (20 * A (qStar G σ R) + 10 * cb) * minimaxRisk G σ R)) ∧
    (∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : WGraph V E), G.IsConnected → 2 ≤ Fintype.card V →
      ∀ (σ R : ℝ), 0 < σ → 0 < R → qStar G σ R = Fintype.card V →
        (⨆ f : V → ℝ, ⨆ _ : MaxCompForest.fnEnergy G f ≤ R ^ 2, blockRisk G σ (PMF.pure ⊥) f) ≤
          10 * minimaxRisk G σ R) ∧
    (∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : WGraph V E), G.IsConnected → 2 ≤ Fintype.card V →
      ∀ (σ : ℝ), 0 < σ → ∀ Q : Finpartition (Finset.univ : Finset V), Q.parts.card = 1 →
        (⨆ f : V → ℝ, ⨆ _ : MaxCompForest.fnEnergy G f ≤ (0 : ℝ) ^ 2, blockRisk G σ (PMF.pure Q) f) =
          ENNReal.ofReal (σ ^ 2)) ∧
    (∃ C : ℝ, 0 < C ∧
      ∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : WGraph V E), G.IsConnected → 2 ≤ Fintype.card V →
        ∀ (σ R : ℝ), 0 < σ → 0 < R →
          ∃ μ : PMF (Finpartition (Finset.univ : Finset V)),
            (∀ Q ∈ μ.support, Q.parts.card ≤ min (Fintype.card V) (2 * qStar G σ R)) ∧
            (⨆ f : V → ℝ, ⨆ _ : MaxCompForest.fnEnergy G f ≤ R ^ 2, blockRisk G σ μ f) ≤
              ENNReal.ofReal (C * Real.log ((qStar G σ R : ℝ) + 1)) * minimaxRisk G σ R) := by sorry

end MaxCompForest.Supplement
