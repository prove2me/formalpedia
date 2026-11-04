-- Prove2me | Theorems.Thm_GOLiQ_lemma_3
-- name    : GOLiQ.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:50:58.041701+00:00
-- url     : https://prove2.me/theorems/2b347f94-c180-476d-8d1d-85e2bf349863
-- title:
--   Lemma 3 — pathwise Lipschitz continuity of waiting times in the rates
-- statement:
--   Let $U_n,V_n\ge0$ and consider two waiting-time sequences with the same inputs and rate sequences $(\mu_n,\lambda_n)$ and $(\tilde\mu_n,\tilde\lambda_n)$:
--   $$W_n=\Big(W_{n-1}+\frac{V_n}{\mu_n}-\frac{U_n}{\lambda_n}\Big)^+,\qquad \tilde W_n=\Big(\tilde W_{n-1}+\frac{V_n}{\tilde\mu_n}-\frac{U_n}{\tilde\lambda_n}\Big)^+,\qquad n\ge1,$$
--   from initial values $W_0,\tilde W_0\ge0$. Suppose $\underline\mu\le\mu_n,\tilde\mu_n$ and $\underline\lambda\le\lambda_n,\tilde\lambda_n$, and that there are constants $c_\mu,c_\lambda>0$ with $|\mu_n-\tilde\mu_n|\le c_\mu$ and $|\lambda_n-\tilde\lambda_n|\le c_\lambda$ for all $n\ge1$. Then for all $n\ge1$
--   $$|W_n-\tilde W_n|\le|W_0-\tilde W_0|+\Big(\frac{c_\mu}{\underline\mu}+\frac{c_\lambda}{\underline\lambda}\Big)\max(X_n,\tilde X_n)+\frac{c_\mu}{\underline\mu}\max(W_n,\tilde W_n),$$
--   where $X_n$, $\tilde X_n$ are the observed busy periods, following recursion (7) from any initial values $X_0,\tilde X_0\ge0$.
--
--   This is the pathwise estimate that controls the transient error during the warm-up period of each cycle.
--
--   Differences from the source:
--   - generalization: (µₙ, λₙ), (µ̃ₙ, λ̃ₙ) ∈ B with the bounds µ̲ and λ̲ (λ̲ not defined in the paper) → any positive lower bounds µ̲ ≤ µₙ, µ̃ₙ and λ̲ ≤ λₙ, λ̃ₙ; reason: rates from B satisfy them with µ̲ and λ̲ = λ(p̄)
--   - generalization: random sequences Uₙ, Vₙ (the bound holds almost surely) → every deterministic path uₙ, vₙ ≥ 0; reason: the statement is pathwise; the random case is its instance at each ω
--   - encoding: initial waiting times W₀, W̃₀ → W₀, W̃₀ ≥ 0; reason: waiting times are nonnegative
-- source:
--   Chen, Liu, Hong, An Online Learning Approach to Dynamic Pricing and Capacity Sizing in Service Systems, arXiv:2009.02911v3, Lemma 3, pp.25–26

import Mathlib
import Definitions.Def_GOLiQ_lindley

namespace GOLiQ

/-- **Lemma 3 (Lipschitz continuity)** (Chen, Liu, Hong, arXiv:2009.02911v3, pp.25–26), a pathwise
statement. Two waiting time sequences driven by the same `Uₙ, Vₙ` and rate sequences `(µₙ, λₙ)`,
`(µ̃ₙ, λ̃ₙ)`:

`Wₙ = (Wₙ₋₁ + Vₙ/µₙ − Uₙ/λₙ)⁺`,  `W̃ₙ = (W̃ₙ₋₁ + Vₙ/µ̃ₙ − Uₙ/λ̃ₙ)⁺`,  `n ≥ 1`,

with `|µₙ − µ̃ₙ| ≤ c_µ`, `|λₙ − λ̃ₙ| ≤ c_λ` (`c_µ, c_λ > 0`) satisfy, for all `n ≥ 1`,

`|Wₙ − W̃ₙ| ≤ |W₀ − W̃₀| + (c_µ/µ̲ + c_λ/λ̲) max(Xₙ, X̃ₙ) + (c_µ/µ̲) max(Wₙ, W̃ₙ)`,

where `Xₙ, X̃ₙ` are the observed busy periods, following (7) from any initial values `X₀, X̃₀ ≥ 0`.

**Formalization Note.** `µ̲` and `λ̲` are any positive lower bounds of the service and arrival rates
(the paper's rates lie in `B`, so `µ̲` and `λ̲ = λ(p̄)` qualify). The inputs `Uₙ, Vₙ ≥ 0` are an
arbitrary deterministic path; `W₀, W̃₀ ≥ 0`. -/
theorem lemma_3 (u v : ℕ → ℝ) (hu : ∀ n, 1 ≤ n → 0 ≤ u n) (hv : ∀ n, 1 ≤ n → 0 ≤ v n)
    (mu mu' la la' : ℕ → ℝ) (muLo laLo : ℝ) (hmuLo : 0 < muLo) (hlaLo : 0 < laLo)
    (hmu : ∀ n, 1 ≤ n → muLo ≤ mu n) (hmu' : ∀ n, 1 ≤ n → muLo ≤ mu' n)
    (hla : ∀ n, 1 ≤ n → laLo ≤ la n) (hla' : ∀ n, 1 ≤ n → laLo ≤ la' n)
    (cmu cla : ℝ) (hcmu : 0 < cmu) (hcla : 0 < cla)
    (hdmu : ∀ n, 1 ≤ n → |mu n - mu' n| ≤ cmu) (hdla : ∀ n, 1 ≤ n → |la n - la' n| ≤ cla)
    (W₀ W₀' X₀ X₀' : ℝ) (hW₀ : 0 ≤ W₀) (hW₀' : 0 ≤ W₀') (hX₀ : 0 ≤ X₀) (hX₀' : 0 ≤ X₀')
    (n : ℕ) (hn : 1 ≤ n) :
    |(lindley W₀ X₀ (fun j => v j / mu j) (fun j => u j / la j) n).1 -
        (lindley W₀' X₀' (fun j => v j / mu' j) (fun j => u j / la' j) n).1| ≤
      |W₀ - W₀'| +
        (cmu / muLo + cla / laLo) *
          max (lindley W₀ X₀ (fun j => v j / mu j) (fun j => u j / la j) n).2
            (lindley W₀' X₀' (fun j => v j / mu' j) (fun j => u j / la' j) n).2 +
        (cmu / muLo) *
          max (lindley W₀ X₀ (fun j => v j / mu j) (fun j => u j / la j) n).1
            (lindley W₀' X₀' (fun j => v j / mu' j) (fun j => u j / la' j) n).1 := by sorry

end GOLiQ
