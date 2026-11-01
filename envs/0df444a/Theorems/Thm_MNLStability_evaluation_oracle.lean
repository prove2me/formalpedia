-- Prove2me | Theorems.Thm_MNLStability_evaluation_oracle
-- name    : MNLStability.evaluation_oracle
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:31:12.739184+00:00
-- url     : https://prove2.me/theorems/3823a967-b36e-425b-a6e6-ec73be5b89ae
-- title:
--   §2.3 — the sampling evaluation oracle (corrected: a factor $s$ for reading $M$'s law)
-- statement:
--   There is an absolute constant $c_1>0$ such that the following holds for the program `estimate`. Take $n\ge1$ products with positive weights, non-negative prices, and a finitely supported law of $M$ with $s$ support points, in the sampling-amenable regime $w_{\max}>\varepsilon_0w_0/n$ with $0<\varepsilon_0\le1$. For every inventory vector $U$, every error $e>0$ and every confidence level $\hat\delta>0$:
--
--   1. the estimate $\tilde R$ satisfies $\tilde R\in(1\pm e)\cdot\mathbb E[R(U)]$, that is $|\tilde R-\mathbb E[R(U)]|\le e\,\mathbb E[R(U)]$, with probability at least $1-\hat\delta$;
--   2. every run costs at most
--   $$c_1\bigl(s+n(\|U\|_1+1)\bigr)\Bigl(1+\Bigl(\frac{(\|U\|_1+1)\,n\Delta}{\varepsilon_0e}\Bigr)^2\Bigr)\bigl(1+\log\max\{1,1/\hat\delta\}\bigr)$$
--   unit operations.
--
--   The paper cites the oracle from Aouad et al. (2018b, App. A.2): a random estimate within $(1\pm\varepsilon)$ with probability $1-\delta$ in time polynomial in $n,\|U\|_1,\Delta,1/\varepsilon,1/\delta$. It is how the algorithm selects among its candidates (§3.3).
--
--   Differences from the source:
--   - correction: running time polynomial in n, ‖U‖₁, Δ, 1/ε, 1/δ → an extra factor s + n(‖U‖₁ + 1), with s the number of support points of M; reason: the law of M is part of the input (p.3), and an oracle that never reads it cannot be accurate: two laws that differ only in one support atom of mass 1/s at a huge value change E[R(U)] by a constant factor (n = 2, ‖U‖₁ = 1, Δ = 9), so Ω(s) reads are needed
--   - generalization: polynomial in 1/δ → a factor 1 + log max{1, 1/δ̂}; reason: stronger bound; the Hoeffding sample size depends on log(2/δ̂)
--   - generalization: "there exists an efficient procedure" → the named program estimate, with its counted cost; reason: the program witnesses the existence
--   - reading: R̃ ∈ (1 ± ε)·E[R(U)] → |R̃ − E[R(U)]| ≤ e·E[R(U)]; reason: the closed interval; the open one is empty when E[R(U)] = 0 (U = 0)
--   - reading: running time in an unspecified model → unit-cost real RAM with a geometric draw at cost 1 and a categorical draw over ℓ masses at cost ℓ + 1; reason: the paper fixes no model; with one simulated customer at a time the cost would grow with the value of M
--   - encoding: the regime w_max > εw₀/n of §2.3 with the accuracy ε → a regime parameter ε₀ ∈ (0, 1], separate from the error e; reason: instances in the regime for some ε > 1 are in it for ε₀ = 1; the paper's single ε is the case ε₀ = e
--   - encoding: O(·) → an absolute constant c₁ chosen before the instance; bound on every run; reason: the usual reading of O(·)
-- source:
--   Aouad & Segev, The Stability of MNL-Based Demand under Dynamic Customer Substitution and its Algorithmic Implications, SSRN:3498325 (manuscript of 2019-12-04), §2.3, p.13 ("there exists an efficient procedure …"; cited from Aouad et al. 2018b, App. A.2)

import Mathlib
import Definitions.Def_MNLStability_IsLaw
import Definitions.Def_MNLStability_expX
import Definitions.Def_MNLStability_opt
import Definitions.Def_MNLStability_estimate

namespace MNLStability

/-- **The evaluation oracle** (SSRN:3498325, §2.3, p.13; cited from Aouad et al. 2018b, App. A.2),
for the explicit program `estimate`. There is an absolute constant `c₁ > 0` such that, for every
instance with `n ≥ 1` products, positive weights, non-negative prices and a finitely supported law
`pM` of `M`, in the sampling-amenable regime `w_max > ε₀·w₀/n` with `ε₀ ∈ (0, 1]`, for every
inventory vector `U`, every error `e > 0` and every confidence level `δ̂ > 0`:
1. the estimate `R̃` satisfies `R̃ ∈ (1 ± e)·E[R(U)]` with probability at least `1 − δ̂`;
2. every run costs at most
   `c₁·(s + n(‖U‖₁ + 1))·(1 + ((‖U‖₁ + 1)·nΔ/(ε₀ e))²)·(1 + log max{1, 1/δ̂})` unit operations,
   where `s` is the number of support points of `M`. -/
theorem evaluation_oracle : ∃ c₁ : ℝ, 0 < c₁ ∧
    ∀ (n : ℕ) (wts : Weights n), 1 ≤ n → wts.Pos → ∀ r : Fin n → ℝ, (∀ i, 0 ≤ r i) →
    ∀ pM : ℕ →₀ ℝ, IsLaw pM → ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ ≤ 1 → ε₀ * wts.w0 / n < wts.wmax →
    ∀ (U : Fin n → ℕ) (e δh : ℝ), 0 < e → 0 < δh →
      1 - δh ≤ (((estimate wts r pM U e δh).run 0).toOuterMeasure
          {x | |x.1 - expR wts r pM U| ≤ e * expR wts r pM U}).toReal ∧
      ∀ x ∈ ((estimate wts r pM U e δh).run 0).support,
        (x.2 : ℝ) ≤ c₁ * (supportSize pM + n * (norm1 U + 1)) *
          (1 + ((norm1 U + 1) * n * wts.Delta / (ε₀ * e)) ^ 2) *
            (1 + Real.log (max 1 δh⁻¹)) := by sorry

end MNLStability
