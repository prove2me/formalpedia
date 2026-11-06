-- Prove2me | Theorems.Thm_IntervalToDynamic_theorem_4
-- name    : IntervalToDynamic.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:26:11.065066+00:00
-- url     : https://prove2.me/theorems/9955f20f-207a-41be-89e3-b3de89dad8f2
-- title:
--   Theorem 4 — algorithmic OIR-to-ODR reduction, in all three regimes
-- statement:
--   Fix $d,T\ge1$, $D_{\mathcal X},G>0$, a domain $\mathcal X$ and losses $f_t$, and let $\mathcal Y=\mathcal B(D_{\mathcal X})$. Let $\mathcal A$ be an online algorithm with decisions in $\mathcal Y$, and let $x_t$ be the decisions of Algorithm 1 run with $\mathcal A$. Write $P_T=\sum_{t=2}^T\|u_t-u_{t-1}\|_2$ and $\text{D-Reg}_T(\{u_t\})=\sum_{t=1}^T(f_t(x_t)-f_t(u_t))$. Suppose Assumptions 1 and 2 hold for the selected loss class, and let $R>0$.
--
--   1. **Convex.** If $\mathcal A$ has interval regret $R\sqrt{|I|}$ on $\mathcal Y$ for convex losses, then $x_t\in\mathcal X$ for all $t$ and, for every $\{u_t\}\in\mathcal X^T$,
--   $$
--   \text{D-Reg}_T(\{u_t\})\le R\sqrt{2\Bigl(1+\frac{2P_T}{D_{\mathcal X}}\Bigr)T}.
--   $$
--   2. **Exp-concave.** If $\mathcal A$ has interval regret $Rd(1+\log|I|)$ on $\mathcal Y$ for exp-concave losses, then $x_t\in\mathcal X$ for all $t$ and, with $\rho=Rd(1+\log T)$, for every $\{u_t\}\in\mathcal X^T$,
--   $$
--   \text{D-Reg}_T(\{u_t\})\le\Bigl(2+\frac{H_h}8\Bigr)\Bigl(\rho+\rho^{2/3}P_T^{2/3}(2T)^{1/3}\Bigr).
--   $$
--   3. **Strongly convex.** If $\mathcal A$ has interval regret $R(1+\log|I|)$ on $\mathcal Y$ for strongly convex losses, then the same conclusion holds with $\rho=R(1+\log T)$ and the $H_h$ of this mode.
--
--   In the paper's notation these are $\widetilde{\mathcal O}(\sqrt{(1+P_T)T})$, $\widetilde{\mathcal O}(d+d^{2/3}P_T^{2/3}T^{1/3})$ and $\widetilde{\mathcal O}(1+P_T^{2/3}T^{1/3})$. An algorithm with optimal interval regret on the enlarged ball thus yields a proper algorithm with optimal dynamic regret on an arbitrary compact convex domain.
--
--   **Formalization Note** The losses of the class on $\mathcal Y$ are those of `LossClass`, with the coefficients of Table 2.
--
--   Differences from the source:
--   - reading: interval regret of order Õ(√|I|), Õ(d log|I|), Õ(log|I|); D-Reg_T = Õ(√((1 + P_T)T)), Õ(d + d^{2/3} P_T^{2/3} T^{1/3}), Õ(1 + P_T^{2/3} T^{1/3}) → for every R > 0, guarantees R √n, R d (1 + log n), R (1 + log n) imply the explicit bounds of the statement; reason: R carries the logarithmic factors hidden by Õ and may depend on T, with log read as at least one (p.4); the constants depend only on D_X, G, α, λ (p.9), and each bound is at most a constant times the printed rate times a power of R (1 + log T), so the Lean statement implies Theorem 4
--   - reading: any algorithm A on Y → a deterministic map `A` from histories to Y, with the guarantee over all loss sequences of `LossClass`; reason: the surrogates are adaptive, so the guarantee must hold against all sequences of the class; T is fixed before A; for a randomized A, the milestones `sec32_convex_rate` and `sec32_curved_rate` are pathwise and apply to each seed
--   - generalization: f_t differentiable on the domain, with gradient ∇f_t → any gradient oracle with `HasGradientWithinAt` on the domain; reason: the domain may have empty interior; the gradient of a differentiable loss is such an oracle, so the printed case is included
--   - encoding: X compact convex, with Π_X and X^T presupposing a point → `X.Nonempty` inside `SatisfiesAssumptions`; reason: Π_X and comparators in X need a point; no instance of the paper is excluded
--   - encoding: rounds t ∈ [T], d and T positive integers → round 0 unused; `0 < d`, `1 ≤ T`; reason: the paper's conventions
-- source:
--   Wang–Zhao–Zhou, On the Relation Between Interval Regret and Dynamic Regret, arXiv:2609.34423, Theorem 4, p.8

import Mathlib
import Definitions.Def_IntervalToDynamic_wrapperX
import Definitions.Def_IntervalToDynamic_SatisfiesAssumptions
import Definitions.Def_IntervalToDynamic_LossClass
import Definitions.Def_IntervalToDynamic_Hh
import Definitions.Def_IntervalToDynamic_HasIntervalRegret
import Definitions.Def_ModernOnlineLearning_Dynamic_Defs
open ModernOnlineLearning.Dynamic (dynamicRegret pathLength)

namespace IntervalToDynamic

/-- Theorem 4 (algorithmic OIR-to-ODR reduction). Wang–Zhao–Zhou, *On the Relation Between Interval Regret and Dynamic Regret*, arXiv:2609.34423, Theorem 4, p.8.

Suppose Assumptions 1 and 2 hold for the selected loss class. For any algorithm `A` which guarantees
interval regret of order `Õ(√|I|)`, `Õ(d log|I|)`, or `Õ(log|I|)` on the enlarged domain
`Y = B(D_X)` for convex, exp-concave, or strongly convex losses respectively, Algorithm 1 produces
proper decisions `x_t ∈ X` and, for any comparator sequence `u ∈ X^T`,
`D-Reg_T(u) = Õ(√((1 + P_T) T))`, `Õ(d + d^{2/3} P_T^{2/3} T^{1/3})`, `Õ(1 + P_T^{2/3} T^{1/3})`.

**Formalization Note.** `Õ` is read with an explicit factor `R > 0`, which carries its hidden
factors and may depend on `T`: the guarantee of `A` is `R √n`, `R d (1 + log n)`, `R (1 + log n)` at
`n = |I|` (logarithms are at least one, p.4), and the conclusion is an explicit bound with
constants depending only on `D_X`, `G`, `α`, `λ` (`H_h` of Table 2), with
`ρ = R d (1 + log T)`, respectively `ρ = R (1 + log T)`. `T` is fixed before `A`, as a horizon-aware `A`
requires. `A` is deterministic, a map from histories to `Y`; rounds are numbered from 1. The losses
come with a gradient oracle `g`, see `SatisfiesAssumptions`. -/
theorem theorem_4 {d : ℕ} (hd : 0 < d) (T : ℕ) (hT : 1 ≤ T) (X : Set (EuclideanSpace ℝ (Fin d))) (DX G : ℝ)
    (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (g : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (A : OnlineAlgorithm (EuclideanSpace ℝ (Fin d)))
    (hAY : ∀ l, A l ∈ Metric.closedBall 0 DX) :
    ((∀ t ∈ Finset.Icc 1 T, SatisfiesAssumptions LossMode.convex X DX G (f t) (g t)) →
      ∀ R : ℝ, 0 < R →
      HasIntervalRegret A (Metric.closedBall 0 DX) (LossClass LossMode.convex DX G) T
        (fun n => R * Real.sqrt n) →
      (∀ t ∈ Finset.Icc 1 T, wrapperX LossMode.convex X DX G A g t ∈ X) ∧
      ∀ u : ℕ → EuclideanSpace ℝ (Fin d), (∀ t ∈ Finset.Icc 1 T, u t ∈ X) →
        dynamicRegret f (wrapperX LossMode.convex X DX G A g) u T ≤
          R * Real.sqrt (2 * (1 + 2 * pathLength u T / DX) * T)) ∧
    (∀ α : ℝ,
      (∀ t ∈ Finset.Icc 1 T, SatisfiesAssumptions (LossMode.expConcave α) X DX G (f t) (g t)) →
      ∀ R : ℝ, 0 < R →
      HasIntervalRegret A (Metric.closedBall 0 DX) (LossClass (LossMode.expConcave α) DX G) T
        (fun n => R * d * (1 + Real.log n)) →
      (∀ t ∈ Finset.Icc 1 T, wrapperX (LossMode.expConcave α) X DX G A g t ∈ X) ∧
      ∀ u : ℕ → EuclideanSpace ℝ (Fin d), (∀ t ∈ Finset.Icc 1 T, u t ∈ X) →
        dynamicRegret f (wrapperX (LossMode.expConcave α) X DX G A g) u T ≤
          (2 + Hh (LossMode.expConcave α) DX G / 8) *
            (R * d * (1 + Real.log T) + (R * d * (1 + Real.log T)) ^ (2 / 3 : ℝ) *
              pathLength u T ^ (2 / 3 : ℝ) * (2 * (T : ℝ)) ^ (1 / 3 : ℝ))) ∧
    (∀ lam : ℝ,
      (∀ t ∈ Finset.Icc 1 T, SatisfiesAssumptions (LossMode.stronglyConvex lam) X DX G (f t) (g t)) →
      ∀ R : ℝ, 0 < R →
      HasIntervalRegret A (Metric.closedBall 0 DX) (LossClass (LossMode.stronglyConvex lam) DX G) T
        (fun n => R * (1 + Real.log n)) →
      (∀ t ∈ Finset.Icc 1 T, wrapperX (LossMode.stronglyConvex lam) X DX G A g t ∈ X) ∧
      ∀ u : ℕ → EuclideanSpace ℝ (Fin d), (∀ t ∈ Finset.Icc 1 T, u t ∈ X) →
        dynamicRegret f (wrapperX (LossMode.stronglyConvex lam) X DX G A g) u T ≤
          (2 + Hh (LossMode.stronglyConvex lam) DX G / 8) *
            (R * (1 + Real.log T) + (R * (1 + Real.log T)) ^ (2 / 3 : ℝ) *
              pathLength u T ^ (2 / 3 : ℝ) * (2 * (T : ℝ)) ^ (1 / 3 : ℝ))) := by sorry

end IntervalToDynamic
