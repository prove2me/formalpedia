-- Prove2me | Theorems.Thm_OnlineBeckFiala_proposition_2_7
-- name    : OnlineBeckFiala.proposition_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:34:48.424091+00:00
-- url     : https://prove2.me/theorems/19a0ecf8-ae4b-4dad-8fab-bf4ba3fda874
-- title:
--   Proposition 2.7 — balance with probability $1-\theta$ gives an online signing with prefix sums $\le6L$ except with probability $3T\theta$
-- statement:
--   Let $V\subseteq\mathbb R^n$ be a family of vectors, $L>0$, and let $\mu$ be a probability density on $\mathbb R^n$, positive on $(-L,L)^n$ and zero off it, such that
--   $$\sup_{v\in V}P_{X\sim\mu}\{X\text{ is not }v\text{-balanced}\}\le\theta\qquad(8)$$
--   for some $\theta\in[0,\infty]$. Then there is a randomized online signing algorithm, with signs $\varepsilon_t\in\{-1,1\}$, such that for every $T$ and every fixed sequence $v_1,\dots,v_T\in V$,
--   $$P\Bigl\{\max_{k\le T}\Bigl\|\sum_{t\le k}\varepsilon_tv_t\Bigr\|_\infty>6L\Bigr\}\le3T\theta\qquad(9).$$
--
--   This is the algorithmic core: any invariant density on the cube whose states are balanced with high probability yields an online signing whose prefix sums stay bounded.
--
--   **Formalization Note** The algorithm is an online signer in the sense of the mission's definition, chosen before $T$ and the sequence. Times are 0-based and the event is over every prefix.
--
--   Differences from the source:
--   - generalization: a product law µ supported on (−L, L)^n (in §2.1, µ = ρ^{⊗n} with ρ a positive density) → any measurable probability density µ on ℝ^n, positive on (−L, L)^n and zero off it; reason: the proof uses only Lemma 2.2, which holds for every such density; every product of positive densities on (−L, L) is one
--   - encoding: L the half-width of the interval (−L, L) → hypothesis 0 < L; reason: (−L, L) is an interval in §2.1; for n = 0 the cube is the whole one-point space and does not force L > 0, and with L < 0 the event 6L < 0 would be certain
--   - encoding: θ a real bound on probabilities → θ : ℝ≥0∞; reason: probabilities live in [0, 1]; θ ≥ 0 is implicit in (8)
--   - encoding: v1, …, vT ∈ V and max over k ≤ T → v 0, …, v (T−1) ∈ V and ∃ k < T; reason: 0-based times
-- source:
--   Altschuler, Tikhomirov, Online Beck–Fiala Down to Logarithmic Sparsity, arXiv:2607.14238 (held version, sha256 5a1529d2…), p.5, Proposition 2.7, eqs. (8), (9)

import Mathlib
import Definitions.Def_OnlineBeckFiala_OnlineSigner
import Definitions.Def_OnlineBeckFiala_walkLaw

open MeasureTheory

namespace OnlineBeckFiala

/-- **Proposition 2.7, p.5.** Altschuler, Tikhomirov, *Online Beck–Fiala Down to Logarithmic
Sparsity*, arXiv:2607.14238 (held version, sha256 5a1529d2…): "Let V ⊆ R^n be a family of column
vectors. Suppose a product law µ supported on (−L, L)^n satisfies
sup_{v∈V} P_{X∼µ}{X is not v-balanced} ≤ θ. (8)
Then there is a randomized online vector balancing algorithm such that for every fixed sequence
v1, . . . , vT ∈ V, P{max_{k≤T} ‖∑_{t≤k} εt vt‖∞ > 6L} ≤ 3Tθ. (9)"

**Formalization Note.** `µ` is given by its density, as the balance notion (7) needs: any
probability density on `ℝ^n` (measurable, `∫ µ = 1`) that is positive on the cube `(−L, L)^n` and
zero off it. `L > 0`, as the interval `(−L, L)` of §2.1 presumes (for `n = 0` the cube is the
whole one-point space whatever `L` is, so it does not force `L > 0`). Every product `∏ ρ_i(x_i)`
of positive probability densities on `(−L, L)`, in particular the `ρ^{⊗n}` of §2.1, is one;
the product structure is not required. `θ ∈ [0, ∞]`. The algorithm is an `OnlineSigner n` (±1
signs, online, oblivious input); times are 0-based, `v 0, …, v (T-1) ∈ V`, and the event is over every prefix
`k < T`. -/
theorem proposition_2_7 {n : ℕ} (V : Set (Fin n → ℝ)) (L : ℝ) (hL : 0 < L)
    (μ : (Fin n → ℝ) → ℝ) (hμm : Measurable μ) (hμpos : ∀ x ∈ cube L, 0 < μ x)
    (hμzero : ∀ x ∉ cube L, μ x = 0)
    (hμint : ∫ x, μ x = 1) (θ : ENNReal)
    (h8 : ∀ v ∈ V, densityLaw μ {x | ¬ IsBalanced L μ v x} ≤ θ) :
    ∃ alg : OnlineSigner n, ∀ (T : ℕ) (vs : ℕ → (Fin n → ℝ)), (∀ t < T, vs t ∈ V) →
      alg.P {ω | ∃ k < T, 6 * L < ‖prefixSum alg vs k ω‖} ≤ 3 * (T : ENNReal) * θ := by sorry

end OnlineBeckFiala
