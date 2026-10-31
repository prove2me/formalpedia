-- Prove2me | Theorems.Thm_MWMSLagrange_expected_excess_bound
-- name    : MWMSLagrange.expected_excess_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:03:58.231193+00:00
-- url     : https://prove2.me/theorems/519fec0a-909a-4c13-8485-513da052cbcf
-- title:
--   Proof of Theorem 2, p.24: $\mathbb E[(f_j-\mathbb E f_j)^+]\le 2\sqrt2\bar D\sqrt{T\sum\rho^2\log(1/\delta)}+\delta\bar DT\sum\rho$
-- statement:
--   Let demands $D_{i,t}\in[0,\bar D]$ be independent, $\bar D>0$, let $y_{i,t}\in[0,\bar D]$ be base-stock levels and $\rho_{i,j}\in[0,1]$ fractions, and let $f_j=\sum_{i\in\mathcal N_j}\sum_{t}\rho_{i,j}(y_{i,t}-I_{i,t})^+$ be the weighted base-stock orders at warehouse $j$. For every $\delta\in(0,1)$,
--
--   $$\mathbb E\Big[\Big(f_j-\sum_{i\in\mathcal N_j}\sum_{t=1}^T\rho_{i,j}\,\mathbb E\big[(y_{i,t}-I_{i,t})^+\big]\Big)^+\Big]\le 2\sqrt2\,\bar D\sqrt{T\sum_{i\in\mathcal N_j}\rho_{i,j}^2\log(1/\delta)}+\delta\bar DT\sum_{i\in\mathcal N_j}\rho_{i,j}.$$
--
--   With $\delta=1/(TN)$ this bounds the expected amount by which the orders at warehouse $j$ exceed their mean, which by (3.7) is at most $C_j$.
--
--   Differences from the source:
--   - generalization: the optimal levels and fractions y*_{i,t}(λ*), ρ*_{i,j}(λ*) → any levels y_{i,t} ∈ [0, D̄] and fractions ρ_{i,j} ∈ [0, 1]; reason: the bound uses only Lemma 7 and McDiarmid, not optimality; at (y*, ρ*) it is the page's display
--   - reading: y*_i(λ*) without the period index → y_{i,t}; reason: f_j on the same page is written with y*_{i,t}(λ*); the index t is dropped by a slip
--   - reading: D_{i,t} ≤ D̄ (nonnegativity not written) → each law μ_{i,t} has μ_{i,t}([0, D̄]) = 1; reason: the paper treats demand as nonnegative throughout (lost-sales dynamics; proof of Lemma 7, pp.37–38)
--   - encoding: independent, possibly non-stationary demands D_{i,t} → product measure ⊗_{i,t} μ_{i,t} on ℝ^{[N]×[T]}, D_{i,t}(ω) = ω(i,t); reason: the product of the marginals is the joint law of independent variables
-- source:
--   Miao, Jasin, Chao, Asymptotically Optimal Lagrangian Policies for Multi-Warehouse, Multi-Store Systems with Lost Sales, SSRN 3552995 (manuscript, sha256 1146a7f8…), proof of Theorem 2, p.24, display after "For each j, we can then bound"

import Mathlib
import Definitions.Def_MWMSLagrange_Instance
import Definitions.Def_MWMSLagrange_Instance_Nset
import Definitions.Def_MWMSLagrange_demandMeasure
import Definitions.Def_MWMSLagrange_ubOnHand
import Definitions.Def_MWMSLagrange_orderSum

open MeasureTheory

namespace MWMSLagrange

/-- Miao, Jasin, Chao, SSRN 3552995 (manuscript, sha256 1146a7f8…), proof of Theorem 2, p.24
("For each j, we can then bound"): with independent demands `D_{i,t} ∈ [0, D̄]`, base-stock
levels `y_{i,t} ∈ [0, D̄]`, fractions `ρ_{i,j} ∈ [0, 1]`, a warehouse `j` and `δ ∈ (0, 1)`,
the positive part of the excess of `f_j = ∑_{i∈𝓝_j} ∑_t ρ_{i,j}(y_{i,t} − I_{i,t})^+` over its
mean satisfies
`E[(f_j − ∑_{i∈𝓝_j} ∑_t ρ_{i,j} E[(y_{i,t} − I_{i,t})^+])^+]
  ≤ 2√2 D̄ √(T ∑_{i∈𝓝_j} ρ_{i,j}² log(1/δ)) + δ D̄ T ∑_{i∈𝓝_j} ρ_{i,j}`.

**Formalization Note.** Stated for arbitrary levels in `[0, D̄]` and fractions in `[0, 1]`,
not only for the optimal `(y^*, ρ^*)` of the page (whose `y^*_i(λ^*)` is read as
`y^*_{i,t}(λ^*)`). `I = ubOnHand y`. -/
theorem expected_excess_bound {M N T : ℕ} (I : Instance M N) (Dbar : ℝ) (hD : 0 < Dbar)
    (μ : Fin N → Fin T → Measure ℝ) [∀ i t, IsProbabilityMeasure (μ i t)]
    (hμ : ∀ i t, μ i t (Set.Icc 0 Dbar) = 1)
    (y : Fin N → Fin T → ℝ) (hy : ∀ i t, 0 ≤ y i t ∧ y i t ≤ Dbar)
    (ρ : Fin N → Fin M → ℝ) (hρ : ∀ i j, 0 ≤ ρ i j ∧ ρ i j ≤ 1)
    (j : Fin M) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∫ ω, max (orderSum I y ρ j ω
        - ∑ i ∈ I.Nset j, ∑ t : Fin T,
            ρ i j * ∫ ω', max (y i t - ubOnHand y ω' i t) 0 ∂demandMeasure μ) 0
        ∂demandMeasure μ
      ≤ 2 * Real.sqrt 2 * Dbar * Real.sqrt (T * (∑ i ∈ I.Nset j, ρ i j ^ 2) * Real.log (1 / δ))
        + δ * Dbar * T * ∑ i ∈ I.Nset j, ρ i j := by sorry

end MWMSLagrange
