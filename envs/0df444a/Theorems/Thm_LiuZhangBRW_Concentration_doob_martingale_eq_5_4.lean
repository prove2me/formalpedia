-- Prove2me | Theorems.Thm_LiuZhangBRW_Concentration_doob_martingale_eq_5_4
-- name    : LiuZhangBRW.Concentration.doob_martingale_eq_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:20:14.24172+00:00
-- url     : https://prove2.me/theorems/af87f9ea-38c0-4294-a3a7-ab3338669615
-- title:
--   §5, p. 9 and (5.4) — Doob's martingale of $S_n$: $S_n-\mathbb ES_n=\sum_i\Delta_i$, $\mathbb E_{i-1}\Delta_i=0$
-- statement:
--   Let $X_1,\dots,X_n$ be integrable real random variables on a probability space, $\mathbb E_i=\mathbb E(\cdot\mid X_1,\dots,X_i)$ with $\mathbb E_0=\mathbb E$, and let $\Delta_i=\mathbb E_i(X_i+\dots+X_n)-\mathbb E_{i-1}(X_i+\dots+X_n)$ be Doob's martingale increments. Then, almost surely,
--
--   1. $\displaystyle S_n-\mathbb ES_n=\sum_{i=1}^n\Delta_i$;
--   2. $\mathbb E_{i-1}(\Delta_i)=0$ for $1\le i\le n$, i.e. $\Delta_i$ is a martingale difference;
--   3. for $1\le i\le n$,
--   $$
--   \Delta_i=X_i-\mathbb E_{i-1}X_i+\sum_{\ell=i+1}^n\bigl(\mathbb E_iX_\ell-\mathbb E_{i-1}X_\ell\bigr).\tag{5.4}
--   $$
--
--   This decomposition reduces the tail of $S_n$ to the conditional moments of the increments $\Delta_i$, which (5.4) expresses through the drifts $\mathbb E_iX_\ell-\mathbb E_{i-1}X_\ell$ controlled by the Lipschitz condition.
--
--   **Formalization Note** $\Delta_i$ is `doobIncrement μ X n i`; conditional expectations are given `natF X i`.
--
--   Differences from the source:
--   - encoding: X_1, X_2, ... random variables → X_1, ..., X_n measurable; reason: random variables are measurable; only X_1, ..., X_n enter the statement
--   - encoding: the identities between conditional expectations → almost-sure equalities; reason: conditional expectations are defined up to null sets
--   - encoding: ES_n and E_i(X_i + ⋯ + X_n) presupposed to exist → X_1, ..., X_n integrable; reason: the expectations on p. 9 are defined only for integrable increments, and Lean's integral and condExp return 0 otherwise
-- source:
--   Liu, Zhang, Concentration Inequalities for Branching Random Walks with Applications to Phase Transitions in CSPs, arXiv:1601.04794 (artifact sha256 7499631b9d550f66e791c0b3df0879f26102f111fee3052e363ebbff0c72bdcb; no version stamp), §5, p. 9, unnumbered displays (Δ_i, S_n − ES_n = Σ Δ_i, E_{i−1}(Δ_i) = 0) and (5.4)

import Mathlib
import Definitions.Def_LiuZhangBRW_Concentration_natF
import Definitions.Def_LiuZhangBRW_Concentration_S
import Definitions.Def_LiuZhangBRW_Concentration_doobIncrement

open MeasureTheory

namespace LiuZhangBRW.Concentration

/-- Doob's martingale of `S_n` and the identity (5.4) (Liu, Zhang, *Concentration Inequalities for Branching Random Walks with Applications to
Phase Transitions in CSPs*, arXiv:1601.04794, artifact sha256 7499631b…bdcb,
§5, p. 9, unnumbered displays and (5.4)). With
`Δ_i = E_i(X_i + ⋯ + X_n) − E_{i−1}(X_i + ⋯ + X_n)`, almost surely
1. `S_n − ES_n = ∑_{i=1}^n Δ_i`;
2. `E_{i−1}(Δ_i) = 0` for `1 ≤ i ≤ n`;
3. (5.4) `Δ_i = X_i − E_{i−1}X_i + ∑_{ℓ=i+1}^n (E_iX_ℓ − E_{i−1}X_ℓ)` for `1 ≤ i ≤ n`.

**Formalization Note** `E_i = condExp (natF X i) μ`, `E_0 = E`. The increments
`X_1, …, X_n` are measurable (random variables) and integrable (so that `ES_n` and the
conditional expectations are defined); nothing is assumed about `X_j` for `j > n` or `j = 0`. -/
theorem doob_martingale_eq_5_4 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (n : ℕ)
    (hmeas : ∀ j ∈ Finset.Icc 1 n, Measurable (X j))
    (hint : ∀ j ∈ Finset.Icc 1 n, Integrable (X j) μ) :
    (fun ω => S X n ω - ∫ ω', S X n ω' ∂μ)
        =ᵐ[μ] (fun ω => ∑ i ∈ Finset.Icc 1 n, doobIncrement μ X n i ω) ∧
      (∀ i ∈ Finset.Icc 1 n, condExp (natF X (i - 1)) μ (doobIncrement μ X n i) =ᵐ[μ] 0) ∧
      (∀ i ∈ Finset.Icc 1 n, doobIncrement μ X n i =ᵐ[μ] fun ω =>
        X i ω - condExp (natF X (i - 1)) μ (X i) ω +
          ∑ ℓ ∈ Finset.Ioc i n,
            (condExp (natF X i) μ (X ℓ) ω - condExp (natF X (i - 1)) μ (X ℓ) ω)) := by sorry

end LiuZhangBRW.Concentration
