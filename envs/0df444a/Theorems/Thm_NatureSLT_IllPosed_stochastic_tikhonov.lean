-- Prove2me | Theorems.Thm_NatureSLT_IllPosed_stochastic_tikhonov
-- name    : NatureSLT.IllPosed.stochastic_tikhonov
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:53:06.492158+00:00
-- url     : https://prove2.me/theorems/b7e0fc49-6cb1-4102-a8c9-69c991f74511
-- title:
--   Theorem 7.3 — stochastic ill-posed problems: $P\{\rho_{E_1}(f_\ell, f) > \varepsilon\} \le P\{\rho_{E_2}(F_\ell, F) > \sqrt{\gamma_\ell \mu}\}$
-- statement:
--   Let $E_1, E_2$ be metric spaces (with their Borel $\sigma$-algebras), $A : E_1 \to E_2$ a continuous one-to-one map, and $\Omega$ a regularization functional on $E_1$ (lower semicontinuous, with values in $[0,\infty]$ and compact sets $\{\Omega \le c\}$, $c > 0$). Let $f \in E_1$ with $\Omega(f) < \infty$ solve $A f = F$ (7.20). On a probability space $(S, P)$ let $F_1, F_2, \dots$ be random elements of $E_2$ converging to $F$ in probability,
--
--   $$\lim_{\ell \to \infty} P\{\rho_{E_2}(F_\ell, F) > \varepsilon\} = 0 \quad \forall \varepsilon > 0,$$
--
--   let $\gamma_\ell > 0$ with $\gamma_\ell \to 0$, and let $f_\ell$ be random elements of $E_1$ such that, for every outcome, $f_\ell$ minimizes $W_T(g) = \rho^2_{E_2}(A g, F_\ell) + \gamma_\ell \Omega(g)$ over $E_1$. Then for any positive numbers $\varepsilon$ and $\mu$ there is a positive integer $n(\varepsilon, \mu)$ such that for all $\ell > n(\varepsilon, \mu)$
--
--   $$P\{\rho_{E_1}(f_\ell, f) > \varepsilon\} \le P\{\rho_{E_2}(F_\ell, F) > \sqrt{\gamma_\ell\, \mu}\}. \tag{7.21}$$
--
--   This is the stochastic generalization of Theorem 7.1: it controls the distribution of the error of Method T by the distribution of the error of the data, and so gives consistency in probability whenever $F_\ell$ converges fast enough relative to $\gamma_\ell$.
--
--   **Formalization Note** The random elements $F_\ell$ and $f_\ell$ are assumed Borel measurable (the book's "random functions"), so both events are measurable. The exact solution is assumed to lie in the domain $\{\Omega < \infty\}$ of $\Omega$, which the book assumes tacitly. Every outcome-wise choice of minimizers is allowed. $\ell$ ranges over the natural numbers and $n(\varepsilon,\mu)$ is a positive integer.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, p. 239, Theorem 7.3

import Mathlib
import Definitions.Def_NatureSLT_IllPosed_IsRegularizer
import Definitions.Def_NatureSLT_IllPosed_tikhonovFunctional

namespace NatureSLT.IllPosed

open Filter Topology MeasureTheory
open scoped ENNReal

/-- Theorem 7.3 (Vapnik, *The Nature of Statistical Learning Theory*, 2nd ed., §7.6.2, p. 239;
Vapnik and Stefanyuk 1978). Setting of §7.6.2 (pp. 238–239): `A : E₁ → E₂` is a continuous
one-to-one map between metric spaces, `Ω` a regularization functional (p. 235), `f` an exact
solution of `A f = F` (7.20) in the domain `{Ω < ∞}`. The random right-hand sides
`F_ℓ : S → E₂` on a probability space `(S, P)` are (Borel) measurable and converge to `F` in
probability, `lim_{ℓ→∞} P{ρ_{E₂}(F_ℓ, F) > ε} = 0` for every `ε > 0`; `γ_ℓ > 0` and `γ_ℓ → 0`;
for every `ℓ` and every outcome `ω`, `f_ℓ(ω)` minimizes
`W_T(g) = ρ²_{E₂}(A g, F_ℓ(ω)) + γ_ℓ Ω(g)` over `E₁`, and `f_ℓ` is measurable.
Then for any `ε > 0`, `μ > 0` there is a positive `n(ε, μ)` such that for all `ℓ > n(ε, μ)`,
`P{ρ_{E₁}(f_ℓ, f) > ε} ≤ P{ρ_{E₂}(F_ℓ, F) > √(γ_ℓ μ)}` (7.21). -/
theorem stochastic_tikhonov {E₁ E₂ S : Type*}
    [MetricSpace E₁] [MeasurableSpace E₁] [BorelSpace E₁]
    [MetricSpace E₂] [MeasurableSpace E₂] [BorelSpace E₂]
    [MeasurableSpace S] (P : Measure S) [IsProbabilityMeasure P]
    (A : E₁ → E₂) (hA : Continuous A) (hAinj : Function.Injective A)
    (Ω : E₁ → ℝ≥0∞) (hΩ : IsRegularizer Ω)
    (F : E₂) (f : E₁) (hf : A f = F) (hfΩ : Ω f ≠ ⊤)
    (Fl : ℕ → S → E₂) (hFl_meas : ∀ ℓ, Measurable (Fl ℓ))
    (hFl : ∀ ε : ℝ, 0 < ε → Tendsto (fun ℓ => P {ω | ε < dist (Fl ℓ ω) F}) atTop (𝓝 0))
    (γ : ℕ → ℝ) (hγpos : ∀ ℓ, 0 < γ ℓ) (hγ : Tendsto γ atTop (𝓝 0))
    (fl : ℕ → S → E₁) (hfl_meas : ∀ ℓ, Measurable (fl ℓ))
    (hmin : ∀ ℓ (ω : S) (g : E₁),
      tikhonovFunctional A Ω (γ ℓ) (Fl ℓ ω) (fl ℓ ω) ≤ tikhonovFunctional A Ω (γ ℓ) (Fl ℓ ω) g) :
    ∀ ε : ℝ, 0 < ε → ∀ μ : ℝ, 0 < μ → ∃ n : ℕ, 0 < n ∧ ∀ ℓ : ℕ, n < ℓ →
      P {ω | ε < dist (fl ℓ ω) f} ≤ P {ω | Real.sqrt (γ ℓ * μ) < dist (Fl ℓ ω) F} := by sorry

end NatureSLT.IllPosed
