-- Prove2me | Theorems.Thm_LearnNoConc_ERM_theorem_3_1
-- name    : LearnNoConc.ERM.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:48:41.116986+00:00
-- url     : https://prove2.me/theorems/8178664c-060d-4dd0-8f36-b8b8050dbd85
-- title:
--   Theorem 3.1, p. 14 — ERM over a closed convex class: ‖f̂ − f*‖_{L2} ≤ 2 max{α*_N(γ, δ/4), β*_N(τQ_{F−F}(2τ)/16)} w.p. ≥ 1 − δ − exp(−NQ²_{F−F}(2τ)/2)
-- statement:
--   Let $(X,Y)$ have an arbitrary joint law $\nu$ on $\Omega\times\mathbb R$, with $X\sim\mu$ and $\mathbb EY^2<\infty$. Let $F\subset L_2(\mu)$ be a closed, convex class of functions, let $f^*\in F$ minimize $\mathbb E(f(X)-Y)^2$ over $F$, and put $\xi(X,Y)=f^*(X)-Y$. Let $(X_i,Y_i)_{i=1}^N$ ($N\ge1$) be an i.i.d. sample from $\nu$, and call $\hat f$ an empirical minimizer if it minimizes $\frac1N\sum_{i=1}^N(f(X_i)-Y_i)^2$ over $F$.
--
--   Fix $\tau>0$ for which $Q_{F-F}(2\tau)>0$ and let $\gamma<\tau^2Q_{F-F}(2\tau)/16$. For every $0<\delta<1$, with probability at least $1-\delta-\exp(-NQ_{F-F}^2(2\tau)/2)$, every empirical minimizer $\hat f$ satisfies
--
--   $$\|\hat f-f^*\|_{L_2}\le2\max\Bigl\{\alpha^*_N(\gamma,\delta/4),\ \beta^*_N\Bigl(\frac{\tau Q_{F-F}(2\tau)}{16}\Bigr)\Bigr\}.$$
--
--   Here $Q_{F-F}$ is the small-ball function of $F-F$ (Assumption 3.1), $\beta^*_N$ is the localized Rademacher fixed point of Definition 2.1, and $\alpha^*_N$ is the multiplier fixed point defined after (2.2). This is the main result of the paper: least-squares ERM performs well under a small-ball condition alone, with no boundedness or concentration assumption on the class or the target.
--
--   **Formalization Note** The conclusion bounds the (outer) $\nu^{\otimes N}$-probability of the event "some empirical minimizer is farther than $2\max\{\dots\}$ from $f^*$". $\alpha^*_N$ and $\beta^*_N$ are $[0,\infty]$-valued, so the bound is vacuous when no admissible radius exists. Added hypotheses: $\mathbb EY^2<\infty$ (presupposed by the definition of $f^*$), $N\ge1$, measurability of every $f\in F$ (every $L_2$ class has a measurable representative), and pointwise separability of $F$ (a countable subclass approximating every element pointwise and in $L_2$), which stands in for the measurability of suprema that the paper takes for granted. Closedness is in $L_2(\mu)$. $\gamma$ is not required to be positive, as on the page.
-- source:
--   Mendelson, Learning without Concentration, arXiv:1401.0304v2, Theorem 3.1, p. 14

import Mathlib
import Definitions.Def_LearnNoConc_ERM_Setting

namespace LearnNoConc.ERM

open MeasureTheory
open scoped ENNReal

/-- Theorem 3.1, p. 14: least-squares ERM in a closed convex class under the small-ball
condition. With probability at least `1 − δ − exp(−N Q²_{F−F}(2τ)/2)`, every empirical
minimizer `f̂` satisfies `‖f̂ − f*‖_{L₂} ≤ 2 max{α*_N(γ, δ/4), β*_N(τ Q_{F−F}(2τ)/16)}`. -/
theorem theorem_3_1 {Ω : Type*} [MeasurableSpace Ω] (ν : Measure (Ω × ℝ)) [IsProbabilityMeasure ν]
    (F : Set (Ω → ℝ)) (hFm : ∀ f ∈ F, Measurable f) (hF2 : ∀ f ∈ F, MemLp f 2 (ν.map Prod.fst))
    (hFconv : Convex ℝ F) (hFcl : IsL2Closed (ν.map Prod.fst) F)
    (hFsep : PointwiseSeparable (ν.map Prod.fst) F)
    (hY : MemLp (fun z : Ω × ℝ => z.2) 2 ν) (fstar : Ω → ℝ) (hfstar : fstar ∈ F)
    (hmin : ∀ f ∈ F, ∫ z, (fstar z.1 - z.2) ^ 2 ∂ν ≤ ∫ z, (f z.1 - z.2) ^ 2 ∂ν)
    (N : ℕ) (hN : 0 < N)
    (τ : ℝ) (hτ : 0 < τ) (hQ : 0 < Q (ν.map Prod.fst) (diffSet F) (2 * τ))
    (γ : ℝ) (hγ : γ < τ ^ 2 * Q (ν.map Prod.fst) (diffSet F) (2 * τ) / 16)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (Measure.pi fun _ : Fin N => ν)
      {z | ∃ fhat, IsEmpMin F z fhat ∧
          2 * max (alphaStar ν F fstar N γ (δ / 4))
              (betaStar (ν.map Prod.fst) F fstar N (τ * Q (ν.map Prod.fst) (diffSet F) (2 * τ) / 16))
            < eLpNorm (fhat - fstar) 2 (ν.map Prod.fst)}
      ≤ ENNReal.ofReal (δ + Real.exp (-(N * Q (ν.map Prod.fst) (diffSet F) (2 * τ) ^ 2 / 2))) := by sorry

end LearnNoConc.ERM
