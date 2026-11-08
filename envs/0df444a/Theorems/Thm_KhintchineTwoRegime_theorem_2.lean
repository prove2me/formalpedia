-- Prove2me | Theorems.Thm_KhintchineTwoRegime_theorem_2
-- name    : KhintchineTwoRegime.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:36:08.32388+00:00
-- url     : https://prove2.me/theorems/8652f138-eb69-4276-a03d-301a110e3b0b
-- title:
--   Theorem 2 — six-coordinate regime: $\omega^{(6)}_\tau$ is the unique minimizer on $\tau\in[d_0,d_1]$
-- statement:
--   Let $n\ge6$ and set
--   $$
--   d_0=d_{\max}(4)=\sqrt{2-\sqrt2},\qquad d_1=\sqrt{2-\frac{\sqrt{966}}{22}}.
--   $$
--   For every $\tau\in[d_0,d_1]$, the unique minimizer of $K_n$ on $\mathcal C_n(\tau)$ is
--   $$
--   \omega^{(6)}_\tau=(r,r,r,r,s,s,0,\dots,0),\qquad r=\frac{2-\tau^2}{2\sqrt2},\quad s=\sqrt{\tau^2-\frac{\tau^4}4-\frac12}.
--   $$
--   In particular, writing $q=(2-\tau^2)/\sqrt2$, the minimum is
--   $$
--   \min_{\omega\in\mathcal C_n(\tau)}K_n(\omega)=\frac{3q}4+\frac3{8\sqrt2}\sqrt{1-q^2}.
--   $$
--   The upper endpoint is $d_1=0.7663211842\ldots$, independent of $n$.
--
--   Concretely: (1) $\omega^{(6)}_\tau\in\mathcal C_n(\tau)$; (2) $K_n(\omega^{(6)}_\tau)\le K_n(\omega)$ for all $\omega\in\mathcal C_n(\tau)$; (3) $K_n(\omega)=K_n(\omega^{(6)}_\tau)$ with $\omega\in\mathcal C_n(\tau)$ forces $\omega=\omega^{(6)}_\tau$; (4) the minimum value is as displayed; and $0.7663211842<d_1<0.7663211843$. Together with Theorem 1 this exhibits the phase transition at $d_{\max}(4)$.
--
--   Differences from the source:
--   - encoding: the unique minimizer of K_n on C_n(τ) is ω_τ^{(6)}, with minimum 3q/4 + (3/(8√2))√(1 − q²) → ω_τ^{(6)} ∈ C_n(τ), minimality over C_n(τ), equality of K-values forces ω = ω_τ^{(6)}, and K_n(ω_τ^{(6)}) = A(q); reason: these clauses are the definition of a unique minimizer and of the minimum value
--   - encoding: d₁ = 0.7663211842… → 7663211842/10¹⁰ < d₁ < 7663211843/10¹⁰; reason: a truncated decimal expansion means exactly this two-sided bound
--   - encoding: vectors ω ∈ ℝⁿ with the Euclidean norm ‖·‖₂, coordinates ω₁, …, ωₙ → Fin n → ℝ with the Euclidean norm √(∑ᵢ ωᵢ²) (the published HighDimProb.SparseRecovery.l2Norm), coordinates ω 0, …, ω (n−1); reason: Lean convention (Mathlib's ‖·‖ on Fin n → ℝ is the sup norm); same instances
--   - encoding: E over independent Rademacher signs → uniform average over all sign vectors Fin n → Bool (K); reason: the law of independent Rademacher signs is uniform on {−1, 1}ⁿ; same values
-- source:
--   Fang–Wang, A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), Theorem 2, p.8

import Mathlib
import Definitions.Def_KhintchineTwoRegime_K
import Definitions.Def_KhintchineTwoRegime_Cn
import Definitions.Def_KhintchineTwoRegime_sixProfile
import Definitions.Def_KhintchineTwoRegime_Abound

namespace KhintchineTwoRegime

/-- Theorem 2 (A dimension-free global six-coordinate interval) (Fang–Wang, *A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions*, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), p.8): let `n ≥ 6`,
`d₀ = √(2 − √2)` and `d₁ = √(2 − √966/22)`. For every `τ ∈ [d₀, d₁]` the unique minimizer of
`K_n` on `C_n(τ)` is `ω_τ^{(6)} = (r, r, r, r, s, s, 0, …, 0)`; with `q = (2 − τ²)/√2` the
minimum is `3q/4 + (3/(8√2))√(1 − q²)`. The upper endpoint is `d₁ = 0.7663211842…`,
independent of `n`.

**Formalization Note** "Unique minimizer" is stated as membership `ω_τ^{(6)} ∈ C_n(τ)`,
minimality over `C_n(τ)`, and uniqueness (equality of the `K`-values forces equality of
vectors). The decimal `d₁ = 0.7663211842…` is stated as
`0.7663211842 < d₁ < 0.7663211843`. -/
theorem theorem_2 :
    (∀ n : ℕ, 6 ≤ n →
      ∀ τ ∈ Set.Icc (Real.sqrt (2 - Real.sqrt 2)) (Real.sqrt (2 - Real.sqrt 966 / 22)),
        sixProfile n τ ∈ Cn n τ ∧
        (∀ ω ∈ Cn n τ, K n (sixProfile n τ) ≤ K n ω) ∧
        (∀ ω ∈ Cn n τ, K n ω = K n (sixProfile n τ) → ω = sixProfile n τ) ∧
        K n (sixProfile n τ) = Abound ((2 - τ ^ 2) / Real.sqrt 2)) ∧
    ((7663211842 : ℝ) / 10 ^ 10 < Real.sqrt (2 - Real.sqrt 966 / 22) ∧
      Real.sqrt (2 - Real.sqrt 966 / 22) < (7663211843 : ℝ) / 10 ^ 10) := by sorry

end KhintchineTwoRegime
