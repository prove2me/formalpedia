-- Prove2me | Theorems.Thm_OptimalRLS_Individual_eq_63
-- name    : OptimalRLS.Individual.eq_63
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:19:27.553996+00:00
-- url     : https://prove2.me/theorems/441ad884-a646-4767-9ad0-8d133db952bd
-- title:
--   (63), p. 27 — the excess risk under ρ_s is ‖√T(f − m^(s))‖² = Σₙ (cₙ − sₙ)² γₙ
-- statement:
--   The setting is that of the proof of Theorem 3: Hypothesis 1, a probability measure $\nu$ on $X$ with an eigen-system $(t_n, e_n)$ of $T$ satisfying (17), $B > b$, $\epsilon = (B - b)c$, $\gamma_n$ as there, and a sign sequence $s$. Let $\rho_s$ have marginal $\nu$ and conditional distribution $\mathcal N(m^{(s)}(x), \sigma^2\mathrm{Id})$.
--
--   Then for every $f \in \mathcal H$,
--   $$\mathcal E[f] - \mathcal E[m^{(s)}] = \big\|\sqrt T (f - m^{(s)})\big\|_{\mathcal H}^2 = \sum_{n=1}^\infty (c_n - s_n)^2 \gamma_n, \qquad c_n = \sqrt{\frac{t_n}{\gamma_n}}\,\langle f, e_n\rangle_{\mathcal H}.$$
--
--   Applied to the estimate $f = f_{\mathbf z}^\ell$, this turns the excess risk into a weighted count of sign errors. It is the first step of the reduction to the testing problem of Proposition 7.
--
--   **Formalization Note** $\|\sqrt T h\|^2_{\mathcal H}$ is written as the quadratic form $\int_X \|h(x)\|_Y^2\, d\nu(x)$ (`covForm ν h h`). The page states (63) for $f = f_{\mathbf z}^\ell$; since it is an identity in $f$, it is stated for every $f \in \mathcal H$. Indices start at $0$.
-- source:
--   Caponnetto & De Vito, Found. Comput. Math. 7 (2007), authors' copy, Proof of Th. 3, eq. (63), p. 27

import Mathlib
import Definitions.Def_OptimalRLS_Individual_Model

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace ENNReal

namespace OptimalRLS.Individual

variable {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [TopologicalSpace.SeparableSpace Y] [MeasurableSpace Y] [BorelSpace Y] [FiniteDimensional ℝ Y]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] [MeasurableSpace H] [BorelSpace H] [RKHS ℝ H X Y]

/-- **(63)** (p. 27). In the setting of the proof of Theorem 3, for every sign sequence `s` and
every `f ∈ H` (the page states it for `f = f_z^ℓ`; it is an identity in `f`), with `ρ` the
distribution with marginal `ν` and conditional `N(m^{(s)}(x), σ² Id)`:
`E[f] − E[m^{(s)}] = ‖√T (f − m^{(s)})‖²_H = ∑_n (c_n − s_n)² γ_n`, `c_n = √(t_n/γ_n) ⟨f, e_n⟩_H`.
Here `‖√T h‖²_H` is `covForm ν h h = ∫ ‖h(x)‖² dν`. -/
theorem eq_63 {ι : Type*} (κ : ℝ) (v : HilbertBasis ι ℝ Y) (h1 : Hyp1 X H κ v)
    (M Sig R α β : ℝ) (hM : 0 < M) (hSig : 0 < Sig) (hR : 0 < R) (hα : 0 < α) (hβ : 0 < β)
    (b c : ℝ) (hb : 1 < b) (hc1 : 1 ≤ c) (hc2 : c ≤ 2) (B : ℝ) (hB : b < B)
    (ν : Measure X) [IsProbabilityMeasure ν] (e : ℕ → H) (t : ℕ → ℝ)
    (heig : IsEigenSystem ν e t) (hanti : Antitone t)
    (h17 : ∀ n : ℕ, α ≤ ((n : ℝ) + 1) ^ b * t n ∧ ((n : ℝ) + 1) ^ b * t n ≤ β)
    (s : ℕ → ℝ) (hs : ∀ n, s n = 1 ∨ s n = -1) (f : H) :
    let γ := gam b c ((B - b) * c) α R
    let m := mS e t γ s
    let ρ := rhoS ν m (sig2 M Sig (Module.finrank ℝ Y))
    risk ρ f - risk ρ m = covForm ν (f - m) (f - m) ∧
      covForm ν (f - m) (f - m) = ∑' n, (cn e t γ f n - s n) ^ 2 * γ n := by sorry

end OptimalRLS.Individual
