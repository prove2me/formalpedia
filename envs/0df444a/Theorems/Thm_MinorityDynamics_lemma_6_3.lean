-- Prove2me | Theorems.Thm_MinorityDynamics_lemma_6_3
-- name    : MinorityDynamics.lemma_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:17:28.73821+00:00
-- url     : https://prove2.me/theorems/63e36e87-c748-46b5-8022-1a7c1d52949f
-- title:
--   Lemma 6.3 — multi-step tracking along the lower branch without sources
-- statement:
--   Assume $k\ge 8L$ ($n,k$ odd, $n$ large). There is an absolute constant $C_0>0$ such that the following holds. Let $d\ge1$ be an integer and let $y_0,\dots,y_d$ satisfy $y_0\in\Omega\setminus\{0\}$, $y_{t+1}=f_\ell(y_t)$ for $0\le t<d$, and $y_{d-1}\le 3a/4$. Let $0<\varepsilon\le 1/10$. For the auxiliary chain started at $X'_0=y_0$, with unfolded counts $R_t$,
--   $$\Pr_{y_0}\left(\begin{array}{ll}X'_t>0,\ \Delta(X'_t,y_t)\le\varepsilon&\text{for all }0\le t\le d,\\ X'_t<a&\text{for all }0\le t<d,\\ X'_t=R_t/n<1/2&\text{for all }1\le t\le d\end{array}\right)\ge 1-4e^{-C_0\varepsilon^2kny_0},$$
--   where $\Delta(x,y)=|\ln x-\ln y|$.
--
--   The auxiliary chain follows the deterministic lower-branch trajectory with a multiplicative error at most $e^{\varepsilon}$, without folding, for $d$ steps.
--
--   Differences from the source:
--   - encoding: "all of our statements hold for sufficiently large n" (standing, p.2); n, k odd → ∃ N, ∀ odd n ≥ N, ∀ odd k; reason: the paper's standing convention written out; same instances
--   - encoding: the auxiliary chain X′_t and its unfolded count R_t → the chain on unfolded counts R_t ∈ {0..n}, started at R_0 = n y_0, with X′_t = min{R_t, n − R_t}/n; "X′_t = R_t/n < 1/2" is 2R_t < n; reason: the event concerns both X′_t and R_t; same law and same event
--   - encoding: y_0, …, y_d → a sequence y : ℕ → ℝ constrained at indices 0..d; reason: values beyond d are never used; same instances
-- source:
--   Giakkoupis, Los, Sauerwald, Ziccardi, Minority Dynamics with Small Samples, manuscript (STOC 2027 submission), Lemma 6.3, p.34

import Mathlib
import Definitions.Def_MinorityDynamics_Kernel
import Definitions.Def_MinorityDynamics_Chain
import Definitions.Def_MinorityDynamics_Weights

set_option autoImplicit false

open Classical

namespace MinorityDynamics

/-- **Lemma 6.3 (Multi-step tracking along the lower branch without sources)** (Giakkoupis, Los, Sauerwald, Ziccardi, *Minority Dynamics with Small Samples*, manuscript (STOC 2027 submission), p.34 =
PDF p.36): "Assume k ≥ 8L. Let d ≥ 1 be an integer. Let y0, . . . , yd satisfy y0 ∈ Ω \ {0},
yt+1 = fℓ(yt) (0 ≤ t < d), and assume that yd−1 ≤ 3a/4. Let 0 < ε ≤ 1/10. There is an absolute
constant C0 > 0 such that
Pr_y0( X′t > 0, ∆(X′t, yt) ≤ ε for all 0 ≤ t ≤ d; X′t < a for all 0 ≤ t < d;
X′t = Rt/n < 1/2 for all 1 ≤ t ≤ d ) ≥ 1 − 4e^{−C0 ε² k n y0}."

The event is joint over `t`: for the auxiliary chain started at `X′₀ = y₀`, at every
`0 ≤ t ≤ d` the minority fraction `X′ₜ` is positive and within logarithmic distance `ε` of `yₜ`, it is
below `a` for `t < d`, and for `1 ≤ t ≤ d` no folding occurs (`Rₜ < n/2`, so `X′ₜ = Rₜ/n`).

**Formalization Note** The chain is the auxiliary chain with its unfolded count `Rₜ` as state,
started at `R₀ = n y₀`; `X′ₜ = min{Rₜ, n − Rₜ}/n`. `Δ(x, y) = |ln x − ln y|`. The constant `C₀` is
absolute (chosen before `n`, `k`, `d`, the trajectory and `ε`). The lemma assumes only `k ≥ 8L`
(footnote 5, p.13); the standing "for sufficiently large n" (p.2) is `∃ N`. `n`, `k` odd (p.2). -/
theorem lemma_6_3 :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Odd n → ∀ k : ℕ, Odd k →
      8 * logN n ≤ (k : ℝ) →
      ∀ d : ℕ, 1 ≤ d → ∀ (y : ℕ → ℝ) (s₀ : Fin (n + 1)), InOmega n s₀ → (s₀ : ℕ) ≠ 0 →
        y 0 = ((s₀ : ℕ) : ℝ) / n → (∀ t, t < d → y (t + 1) = fLow k (y t)) →
        y (d - 1) ≤ 3 / 4 * aPt k →
        ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 10 →
          1 - 4 * Real.exp (-(C₀ * ε ^ 2 * k * n * y 0)) ≤
            stayProb (auxKernel n k)
              (fun t => {R | 0 < foldFrac n R ∧ logDist (foldFrac n R) (y t) ≤ ε ∧
                (t < d → foldFrac n R < aPt k) ∧ (1 ≤ t → 2 * (R : ℕ) < n)})
              d s₀ := by sorry

end MinorityDynamics
