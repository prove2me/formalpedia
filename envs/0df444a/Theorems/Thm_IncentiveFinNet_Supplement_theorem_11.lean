-- Prove2me | Theorems.Thm_IncentiveFinNet_Supplement_theorem_11
-- name    : IncentiveFinNet.Supplement.theorem_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:37:58.042833+00:00
-- url     : https://prove2.me/theorems/fef92048-4dbe-4df1-91c6-f7af9a72caa4
-- title:
--   Theorem 11 — with probability $1-e^{-\Omega(n)}$ every sample covariance satisfies $\|\hat\Sigma_i-\Sigma\| = o(1)$
-- statement:
--   Work in the setting of Theorem 5. For every constant $C$ there are $c>0$, a sequence $\varepsilon_n\to0$ and a threshold $N$ such that the following holds for every $n\ge N$. Let $\Sigma\succ0$ satisfy $\|\Sigma\|\le C$ and $\|\Sigma^{-1}\|\le C$ (spectral norm). Let each of the $n$ agents observe $m=\lceil n\log n\rceil$ samples in $\mathbb R^n$, all independent with law $\mathcal N(0,\Sigma)$, and let $\hat\Sigma_i$ be agent $i$'s sample covariance. Then, with probability at least $1-e^{-cn}$,
--   $$
--   \|\hat\Sigma_i-\Sigma\|\le\varepsilon_n\quad\text{for all } i\in[n].
--   $$
--
--   This concentration bound is the probabilistic input to Theorem 5.
--
--   Differences from the source:
--
--   - reading: "with probability at least 1 − e^{−Ω(n)}, ‖Σ̂_i − Σ‖ = o(1)" under the O(1) bounds of Theorem 5 → for every bound C there are c > 0, ε_n → 0 and N, depending only on C, with P(‖Σ̂_i − Σ‖ ≤ ε_n for all i) ≥ 1 − e^{−cn} for every n ≥ N and every Σ with ‖Σ‖, ‖Σ⁻¹‖ ≤ C; reason: the uniform reading of the asymptotic notation is the stronger one and implies the statement for every fixed sequence of settings
--   - reading: the samples, sample covariances and m = ⌈n log n⌉ of Theorem 5 → all n·m samples independent N(0, Σ), sampleCov of each agent's m samples, m = ⌈n ln n⌉; reason: as in Theorem 5 (index reuse in the printed sums, independence, natural logarithm as the strongest reading)
--   - encoding: "under the setting of Theorem 5" (also ‖Γ‖, ‖Γ⁻¹‖ = O(1), all edges allowed) → only the hypotheses on Σ; reason: Γ and the permitted edges do not occur in the claim, which concerns Σ̂_i and Σ only; same instances
--   - encoding: ‖·‖ → opNorm2 (the spectral norm, ‖·‖₂ in the proof, p.44); reason: Lean convention
-- source:
--   Jalan, Chakrabarti, Sarkar, Incentive-Aware Models of Financial Networks, arXiv:2212.06808v3, Theorem 11, A.10, p.44

import Mathlib
import Definitions.Def_IncentiveFinNet_Supplement_sampleCov

open Matrix Filter Topology MeasureTheory ProbabilityTheory

namespace IncentiveFinNet.Supplement

/-- **Theorem 11**, Jalan, Chakrabarti, Sarkar, arXiv:2212.06808v3, A.10, p.44: "Under the setting
of Theorem 5, with probability at least `1 − e^{−Ω(n)}`, we have `‖Σ̂_i − Σ‖ = o(1)` for all
`i ∈ [n]`."

Stated uniformly: for every bound `C` there are `c > 0`, a sequence `ε_n → 0` and a threshold `N`
such that for every `n ≥ N` and every `Σ ≻ 0` with `‖Σ‖, ‖Σ⁻¹‖ ≤ C`, with `m = ⌈n ln n⌉` samples
per agent drawn independently from `N(0, Σ)` (Theorem 5, p.16), the probability that
`‖Σ̂_i − Σ‖ ≤ ε_n` for all `i ∈ [n]` is at least `1 − exp(−c n)`.

**Formalization Note**
* The setting of Theorem 5 (p.16): `‖Σ‖, ‖Σ⁻¹‖ = O(1)` (a bound `C` uniform in `n`), `m = ⌈n ln n⌉`,
  independent `N(0, Σ)` samples, the sample covariances `Σ̂_i` (`sampleCov`). The bounds on `Γ` and
  "all edges are allowed" are also part of that setting, but `Γ` and the edges do not occur in the
  claim, so they are omitted.
* `o(1)` and `Ω(n)` depend only on `C`; `‖·‖` is the spectral norm `opNorm2`. -/
theorem theorem_11 :
    ∀ C : ℝ, ∃ c : ℝ, 0 < c ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∃ N : ℕ, ∀ n ≥ N,
      ∀ Sig : Matrix (Fin n) (Fin n) ℝ, Sig.PosDef → opNorm2 Sig ≤ C → opNorm2 Sig⁻¹ ≤ C →
        1 - Real.exp (-(c * n)) ≤
          (dataLaw n (sampleSize n) Sig
            {x | ∀ i, opNorm2 (sampleCov (x i) - Sig) ≤ ε n}).toReal := by sorry

end IncentiveFinNet.Supplement
