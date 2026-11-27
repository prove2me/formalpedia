-- Prove2me | Theorems.Thm_IncentiveFinNet_Supplement_theorem_5
-- name    : IncentiveFinNet.Supplement.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:37:19.773899+00:00
-- url     : https://prove2.me/theorems/00db836a-f580-5db5-a4e4-e0b2b107f5fd
-- title:
--   Theorem 5 — with $m=\lceil n\log n\rceil$ Gaussian samples per agent, $\hat\eta^*\ge(1-o(1))\eta^*$ with probability $1-e^{-\Omega(n)}$
-- statement:
--   Let all edges be allowed. For every constant $C$ there are $c>0$, a sequence $\varepsilon_n\to0$ and a threshold $N$ such that the following holds for every $n\ge N$. Let $\Sigma\succ0$ and $\gamma_1,\dots,\gamma_n>0$ satisfy
--   $$
--   \|\Sigma\|\le C,\quad \|\Sigma^{-1}\|\le C,\quad \|\Gamma\| = \max_i\gamma_i\le C,\quad \|\Gamma^{-1}\| = \max_i\gamma_i^{-1}\le C .
--   $$
--   Let each agent $i$ observe $m=\lceil n\log n\rceil$ samples in $\mathbb R^n$, all samples independent with law $\mathcal N(0,\Sigma)$, and let $\hat\Sigma_i$ be agent $i$'s sample covariance. Let $\hat\eta^*$ be the maximum dampening factor $2/\lambda_{\max}$ of Theorem 4 for the covariances $(\hat\Sigma_i)_{i\in[n]}$, and $\eta^*$ the one with $\Sigma$ in place of every $\hat\Sigma_i$. Then, with probability at least $1-e^{-cn}$, every $\hat\Sigma_i$ is positive definite and
--   $$
--   \hat\eta^*\ \ge\ (1-\varepsilon_n)\,\eta^* .
--   $$
--
--   Agents who estimate their covariances from about $n\log n$ samples can therefore use almost the same dampening factors as agents who know $\Sigma$, so pairwise negotiations still converge fast.
--
--   Differences from the source:
--
--   - reading: "‖Σ‖, ‖Σ⁻¹‖, ‖Γ‖, ‖Γ⁻¹‖ are O(1) with respect to n", "o(1)", "Ω(n)", "for large enough n" → for every bound C there are c > 0, ε_n → 0 and N, depending only on C, such that the bound holds for every n ≥ N and every (Σ, γ) with the four norms ≤ C; reason: the asymptotic notation leaves the dependence of the constants open; the uniform reading is the stronger one and implies the statement for every fixed sequence of settings, and the proof's constants (Vershynin's and the O(1) bounds) depend only on C
--   - reading: µ̂ = (1/m) Σ_i X_i and Σ̂_i = 1/(m − 1) Σ_i (X_i − µ̂)(X_i − µ̂)ᵀ → the sample mean and sample covariance of agent i's m samples (the columns of X_i); reason: the printed sums reuse the agent index i for the samples, as the proof of Theorem 11 (p.44) writes X_1, …, X_m
--   - reading: "each sample column of X_i is drawn independently from N(0, Σ)" → all n·m samples are independent with law N(0, Σ); reason: the natural reading of the independence assumption
--   - reading: m = ⌈n log n⌉ → m = ⌈n ln n⌉ (natural logarithm); reason: the base is not printed; ln n is the smallest of the usual choices, so this is the strongest reading
--   - encoding: the event "η̂* ≥ (1 − o(1))η*" → every Σ̂_i is positive definite and η̂* ≥ (1 − ε_n)η*; reason: η̂* is defined (Theorem 4 needs a network setting, Σ̂_i ≻ 0) only on that event; same instances
--   - encoding: ‖·‖, Γ, η* = 2/λ_max → opNorm2 (the spectral norm), max_i γ_i and max_i γ_i⁻¹, etaStarAll (2 / lamMax of the all-edges setting); reason: Lean convention; same quantities
-- source:
--   Jalan, Chakrabarti, Sarkar, Incentive-Aware Models of Financial Networks, arXiv:2212.06808v3, Theorem 5, §2.3, p.16; proof in A.10, pp.42–44 (Lemmas 3–4, Theorem 11)

import Mathlib
import Definitions.Def_IncentiveFinNet_NetworkSetting
import Definitions.Def_IncentiveFinNet_Supplement_lamMax
import Definitions.Def_IncentiveFinNet_Supplement_sampleCov

open Matrix Filter Topology MeasureTheory ProbabilityTheory

namespace IncentiveFinNet.Supplement

/-- **Theorem 5 (Small Sample Sizes are Sufficient for Fast Convergence)**, Jalan, Chakrabarti,
Sarkar, arXiv:2212.06808v3, §2.3, p.16 (proved in A.10, pp.42–44): "Suppose that `‖Σ‖`, `‖Σ⁻¹‖`,
`‖Γ‖`, and `‖Γ⁻¹‖` are `O(1)` with respect to `n` and all edges are allowed. Also, suppose that each
sample column of `X_i` is drawn independently from a `N(0, Σ)` distribution, and let
`µ̂ = (1/m) Σ_i X_i` and `Σ̂_i := 1/(m − 1) Σ_i (X_i − µ̂)(X_i − µ̂)ᵀ`. Let `η̂*` be the maximum dampening
factor using `(Σ̂_i)_{i∈[n]}` as defined in Theorem 4. Let `η*` be the dampening factor if `Σ̂_i` were
replaced by `Σ` for all `i`. If `m = ⌈n log n⌉`, then for large enough `n`,
`η̂* ≥ (1 − o(1))η*` with probability at least `1 − exp(−Ω(n))`."

Stated uniformly: for every bound `C` there are `c > 0`, a sequence `ε_n → 0` and a threshold `N`
such that for every `n ≥ N`, every `Σ ≻ 0` and every `γ > 0` with `‖Σ‖, ‖Σ⁻¹‖ ≤ C` and
`γ_i, γ_i⁻¹ ≤ C`, with `m = ⌈n ln n⌉` samples per agent drawn independently from `N(0, Σ)`, the
probability that every `Σ̂_i` is positive definite and `η̂* ≥ (1 − ε_n) η*` is at least
`1 − exp(−c n)`.

**Formalization Note**
* "`O(1)` with respect to `n`" is a bound `C` uniform in `n`; the `o(1)` sequence, the `Ω(n)`
  constant `c` and the threshold "large enough `n`" depend only on `C`. This uniform reading implies
  the reading for one fixed sequence of settings.
* `‖·‖` is the spectral norm `opNorm2`; `‖Γ‖ = max_i γ_i` and `‖Γ⁻¹‖ = max_i γ_i⁻¹`.
* All edges are allowed (`J_i = [n]`); `η*` and `η̂*` are `2/λ_max` of Theorem 4 (`etaStarAll`).
* `log` is the natural logarithm. The samples of agent `i` are `x i k`, `k < m`; all `n·m` samples
  are independent (`dataLaw`). The event includes that every `Σ̂_i` is positive definite, which
  `η̂*` presupposes. -/
theorem theorem_5 :
    ∀ C : ℝ, ∃ c : ℝ, 0 < c ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∃ N : ℕ, ∀ n ≥ N,
      ∀ (Sig : Matrix (Fin n) (Fin n) ℝ) (γ : Fin n → ℝ) (hγ : ∀ i, 0 < γ i),
        Sig.PosDef → opNorm2 Sig ≤ C → opNorm2 Sig⁻¹ ≤ C → (∀ i, γ i ≤ C) → (∀ i, (γ i)⁻¹ ≤ C) →
        1 - Real.exp (-(c * n)) ≤
          (dataLaw n (sampleSize n) Sig
            {x | (∀ i, (sampleCov (x i)).PosDef) ∧
              (1 - ε n) * etaStarAll γ hγ (fun _ => Sig) ≤
                etaStarAll γ hγ (fun i => sampleCov (x i))}).toReal := by sorry

end IncentiveFinNet.Supplement
