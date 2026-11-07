-- Prove2me | Theorems.Thm_IIDMatchHard_lemma_B_1
-- name    : IIDMatchHard.lemma_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:05:15.611098+00:00
-- url     : https://prove2.me/theorems/df226edb-dcd0-404c-9851-ae430d5707db
-- title:
--   Lemma B.1 — sums over Poisson arrivals as time integrals
-- statement:
--   Consider the Poisson arrival process of rate $R>0$ with i.i.d. types drawn from a distribution $p$ on a finite set $Y$, so type $y$ has rate $\lambda_y=Rp(y)$. For $\ell\ge0$, let $F_\ell$ map an $\ell$-tuple of types and a time in $[0,1]$ to $[0,1]$, measurably in the time. Then for every type $y$,
--   $$\mathbb E\Big[\sum_{k\ge1:\ \tau_k\le1}\mathbf 1[y_k=y]\,F_{k-1}(y_1,\dots,y_{k-1},\tau_k)\Big]=\lambda_y\int_0^1\mathbb E\big[F_{K(t)}(y_1,\dots,y_{K(t)},t)\big]\,dt.$$
--
--   This compensator identity turns the expected gain collected at arrivals into a time integral. It yields the blocking bound (Lemma B.2) and the Poisson value formula (Lemma 3.5).
--
--   Differences from the source:
--   - generalization: the arrival process of I(G, λ) (rate R = n + 2mλ, probabilities λ_y/R) → any rate R > 0 and any probability vector p on a finite type set, with λ_y = R·p(y); reason: the paper process is the case R = n + 2mλ, p(y) = λ_y/R
--   - reading: F_ℓ maps tuples and times to [0, 1] (expectations of these functions are taken) → F_ℓ(ys, ·) is measurable for every ℓ and ys; reason: the expectations presuppose measurability
--   - encoding: arrivals k ≥ 1 with times τ_k and types y_k → 0-based arrivals k ≥ 0: arrTime ω k = τ_{k+1}, arrType ω k = y_{k+1}, earlier types a Fin k tuple; reason: Lean convention; same sum
--   - encoding: expectations of nonnegative quantities → lower Lebesgue integrals in ℝ≥0∞ (∫⁻) with ENNReal.ofReal; reason: the integrands are nonnegative; same values
--   - encoding: K(t) = number of points in [0, t] → Set.ncard of {k : τ_{k+1} ≤ t}; reason: differs only on a null event (infinitely many points, or a negative gap)
-- source:
--   Teng, Yang, Computational Hardness of Online Stochastic Matching (manuscript of Nov. 3, 2026, sha256 f0193d92…), Lemma B.1, p.14 (PDF p.15)

import Definitions.Def_IIDMatchHard_Poisson

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace IIDMatchHard

/-- **Lemma B.1.** For `ℓ ≥ 0`, let `F_ℓ` map an `ℓ`-tuple of types and a time in `[0, 1]` to
`[0, 1]`. Then for every type `y`,
`E[∑_{k ≥ 1 : τ_k ≤ 1} 1[y_k = y] F_{k−1}(y_1, …, y_{k−1}, τ_k)] = λ_y ∫₀¹ E[F_{K(t)}(y_1, …, y_{K(t)}, t)] dt`,
where `λ_y = R·p(y)` is the rate of type `y`. Teng, Yang, *Computational Hardness of Online Stochastic Matching* (manuscript of Nov. 3, 2026,
sha256 f0193d92…), Lemma B.1, p.14 (PDF p.15).

**Formalization Note.** Arrivals are 0-based: the arrival `k` of the sum is the paper's arrival
`k + 1`, with time `arrTime ω k = τ_{k+1}`, type `arrType ω k = y_{k+1}`, and the tuple of the
`k` earlier types. Stated for any Poisson rate `R > 0` and any type distribution `p` (the paper's
model has `R = n + 2mλ`, `p(y) = λ_y/R`). Both sides are expectations of nonnegative quantities,
written as lower Lebesgue integrals in `ℝ≥0∞`, so no integrability side condition is needed;
`F_ℓ(ys, ·)` is assumed measurable, which the expectations presuppose. -/
theorem lemma_B_1 {Y : Type*} [Fintype Y] [DecidableEq Y] [MeasurableSpace Y]
    [DiscreteMeasurableSpace Y] (R : ℝ) (p : Y → ℝ) (hR : 0 < R) (hp : ∀ y, 0 ≤ p y)
    (hsum : ∑ y, p y = 1) (F : (ℓ : ℕ) → (Fin ℓ → Y) → ℝ → ℝ)
    (hFm : ∀ ℓ ys, Measurable (F ℓ ys))
    (hF : ∀ ℓ ys t, t ∈ Set.Icc (0 : ℝ) 1 → F ℓ ys t ∈ Set.Icc (0 : ℝ) 1) (y : Y) :
    ∫⁻ ω, ∑' k : ℕ, (if arrTime ω k ≤ 1 ∧ arrType ω k = y then
        ENNReal.ofReal (F k (fun i : Fin k => arrType ω i) (arrTime ω k)) else 0)
        ∂ poissonLaw R p =
      ENNReal.ofReal (R * p y) *
        ∫⁻ t in Set.Icc (0 : ℝ) 1, ∫⁻ ω,
          ENNReal.ofReal (F (count ω t) (fun i : Fin (count ω t) => arrType ω i) t)
          ∂ poissonLaw R p := by sorry

end IIDMatchHard
