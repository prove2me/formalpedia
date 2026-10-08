-- Prove2me | Theorems.Thm_KolmogorovChentsov_exists_modification_holderOnWith_Icc
-- name    : KolmogorovChentsov.exists_modification_holderOnWith_Icc
-- status  : Open
-- author  : @Nickrobbins95
-- created : 2026-10-05T01:52:23.523157+00:00
-- url     : https://prove2.me/theorems/54f788be-7689-435b-964f-6756dbc43fc9
-- title:
--   Kolmogorov–Chentsov theorem: a process on $[0,\infty)$ with $\mathbb E\,\rho(X_s,X_t)^p\le M|s-t|^q$, $q>1$, has a locally Hölder modification
-- statement:
--   **Kolmogorov–Chentsov continuity theorem.** Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space, let $(E,\rho)$ be a complete metric space, and let $X=(X_t)_{t\ge 0}$ be a stochastic process indexed by $[0,\infty)$ with values in $E$. Suppose there are constants $p>0$, $q>1$ and $M\ge 0$ such that
--
--   $$
--   \mathbb E\big[\rho(X_s,X_t)^{p}\big]\;\le\; M\,|s-t|^{q}\qquad\text{for all } s,t\ge 0 .
--   $$
--
--   Then $X$ has a modification $Y=(Y_t)_{t\ge 0}$, that is $Y_t=X_t$ almost surely for every $t\ge 0$, with the following property. For every $\omega\in\Omega$, every $T>0$ and every exponent $\gamma$ with $0<\gamma<(q-1)/p$, the path $t\mapsto Y_t(\omega)$ is $\gamma$-Hölder on $[0,T]$: there is a finite constant $C=C(\omega,T,\gamma)$ with
--   $$
--   \rho\big(Y_s(\omega),Y_t(\omega)\big)\;\le\;C\,|s-t|^{\gamma}\qquad\text{for all } s,t\in[0,T] .
--   $$
--   In particular every path of $Y$ is continuous.
--
--   The theorem is the standard way to pass from finite-dimensional distributions to a process with continuous paths, and it needs only a moment bound on pairs of values. For Brownian motion, $\mathbb E|B_t-B_s|^{2m}=C_m|t-s|^m$ for every $m$. Taking $p=2m$ and $q=m$ gives a modification whose paths are Hölder of every order $\gamma<(m-1)/(2m)$, hence of every order $\gamma<1/2$.
--
--   **Formalization Note** The hypothesis is Mathlib's `ProbabilityTheory.IsKolmogorovProcess X P p q M` for a process `X : ℝ≥0 → Ω → E`. It packages three things: the moment bound, written as a lower Lebesgue integral of extended distances `∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P ≤ M * edist s t ^ q`; the positivity of $p$ and $q$; and the Borel measurability of each pair $(X_s,X_t)$ in $E\times E$. That measurability is what makes $\rho(X_s,X_t)$ a random variable when $E$ is not separable. The separate hypothesis `1 < q` is the condition $q>1$. The time set $[0,\infty)$ is `ℝ≥0` with its usual distance, and $[0,T]$ is `Set.Icc 0 T` taken in `ℝ≥0`. The Hölder exponent $\gamma$ is a non-negative real (`ℝ≥0`), coerced to `ℝ` for the comparison with $(q-1)/p$. `HolderOnWith C γ f s` means `edist (f x) (f y) ≤ C * edist x y ^ (γ : ℝ)` for all `x y ∈ s`. "Modification" means exactly `∀ t, Y t =ᵐ[P] X t`; no further measurability of $Y$ is asserted. The Hölder bounds are asserted for every $\omega$, not just almost every $\omega$. The two forms are equivalent, since a modification can be redefined to be constant on a measurable null set.
-- source:
--   D. Revuz and M. Yor, Continuous Martingales and Brownian Motion, 3rd ed., Springer, 1999, Chapter I, Section 2, Theorem (2.1) (Kolmogorov's continuity criterion); O. Kallenberg, Foundations of Modern Probability, 2nd ed., Springer, 2002, Chapter 3, Theorem 3.23 (moments and continuity; Kolmogorov, Loève, Chentsov). This is the one-parameter case (time set [0, infinity), d = 1): E[rho(X_s, X_t)^a] <= M|s - t|^(1+b) with a = p > 0 and b = q - 1 > 0 gives a modification that is locally Hölder of every order c in (0, b/a). The [0, infinity) form follows from Kallenberg's R^1 form applied to t -> X_max(t,0).

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem KolmogorovChentsov.exists_modification_holderOnWith_Icc
    {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    [MetricSpace E] [CompleteSpace E]
    {X : ℝ≥0 → Ω → E} {p q : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (hq : 1 < q) :
    ∃ Y : ℝ≥0 → Ω → E, (∀ t, Y t =ᵐ[P] X t) ∧
      ∀ ω, ∀ T : ℝ≥0, 0 < T → ∀ γ : ℝ≥0, 0 < γ → (γ : ℝ) < (q - 1) / p →
        ∃ C : ℝ≥0, HolderOnWith C γ (fun t ↦ Y t ω) (Set.Icc 0 T) := by sorry
