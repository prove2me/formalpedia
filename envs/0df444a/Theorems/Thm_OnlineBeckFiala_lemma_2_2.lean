-- Prove2me | Theorems.Thm_OnlineBeckFiala_lemma_2_2
-- name    : OnlineBeckFiala.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:34:49.046567+00:00
-- url     : https://prove2.me/theorems/b9d71d9e-3312-48b8-9877-7445aa866eca
-- title:
--   Lemma 2.2 (Stationarity) — the Metropolis walk keeps the law $\mu$
-- statement:
--   Let $L>0$ and let $\mu$ be a probability density on $\mathbb R^n$ that is positive on the cube $(-L,L)^n$ and zero outside it. For non-random vectors $v_1,v_2,\dots\in\mathbb R^n$ let $X_0\sim\mu$ and $X_t=X_{t-1}+\delta_tv_t$ with $P\{\delta_t=s\mid X_{t-1}\}=p^s_{v_t}(X_{t-1})$, where $p^\pm_v,p^0_v$ are the Metropolis probabilities (4)–(6). Then for every such sequence and every $t\ge0$,
--   $$X_t\sim\mu .$$
--
--   Stationarity holds whatever the driving vectors are, which is what makes the walk usable online against an oblivious adversary.
--
--   **Formalization Note** The law of $X_t$ is the initial law pushed through the one-step laws of $v_1,\dots,v_t$; the statement is for every finite list of vectors. "Probability density" is: measurable, integral one.
--
--   Differences from the source:
--   - generalization: µ = ρ^{⊗n} with ρ a positive probability density on (−L, L) → any measurable probability density µ on ℝ^n, positive on (−L, L)^n and zero off it; reason: the proof only uses positivity on the cube and zero outside; ρ^{⊗n} is such a density
--   - encoding: for every sequence v1, v2, … and every t, Xt ∼ µ → for every finite list [v1, …, vt], the folded law walkLaw equals densityLaw µ; reason: the law of Xt depends on v1, …, vt only
-- source:
--   Altschuler, Tikhomirov, Online Beck–Fiala Down to Logarithmic Sparsity, arXiv:2607.14238 (held version, sha256 5a1529d2…), p.4, Lemma 2.2

import Mathlib
import Definitions.Def_OnlineBeckFiala_walkLaw

open MeasureTheory

namespace OnlineBeckFiala

/-- **Lemma 2.2 (Stationarity), p.4.** Altschuler, Tikhomirov, *Online Beck–Fiala Down to Logarithmic
Sparsity*, arXiv:2607.14238 (held version, sha256 5a1529d2…): "For every non-random sequence of
vectors v1, v2, . . . in R^n, Xt ∼ µ."

Setting of §2.1, p.3: `ρ` is a positive probability density on `(−L, L)`, zero outside, and
`µ = ρ^{⊗n}`; `X₀ ∼ µ` and `X_t = X_{t−1} + δ_t v_t` with `P{δ_t = s | X_{t−1}} = p^s_{v_t}(X_{t−1})`.

**Formalization Note.** Stated for every probability density `µ` on `ℝ^n` that is positive on the
cube `(−L, L)^n` and zero off it (measurable, `∫ µ = 1`); the product density `ρ^{⊗n}` of a positive
probability density `ρ` on `(−L, L)` is one. The law of `X_t` after the vectors `vs = [v₁, …, v_t]`
is `walkLaw`, so the claim for every list `vs` is the claim for every sequence and every `t`. -/
theorem lemma_2_2 {n : ℕ} (L : ℝ) (μ : (Fin n → ℝ) → ℝ) (hμm : Measurable μ)
    (hμpos : ∀ x ∈ cube L, 0 < μ x) (hμzero : ∀ x ∉ cube L, μ x = 0)
    (hμint : ∫ x, μ x = 1) (vs : List (Fin n → ℝ)) :
    walkLaw μ L vs = densityLaw μ := by sorry

end OnlineBeckFiala
