-- Prove2me | Theorems.Thm_ImpactCopula_copula_eq_on_rbar
-- name    : ImpactCopula.copula_eq_on_rbar
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:54:45.591394+00:00
-- url     : https://prove2.me/theorems/0ba724b7-91d0-4fab-92ba-11a59dc8e687
-- title:
--   Proof of Theorem 2, "only if" — $C \equiv \hat C$ on $[0,1]\times\overline{\mathcal R}_\theta$
-- statement:
--   Let $\mu$ be a probability measure on $\mathbb R^2$ with marginal distribution function $F_\theta$, and let $C$, $\hat C$ be copulas of $\mu$. Suppose that for every $y \in \mathbb R$,
--
--   $$
--   D_1\hat C\big(u, F_\theta(y)\big) = D_1C\big(u, F_\theta(y)\big) \quad \text{for almost every } u \in [0,1].
--   $$
--
--   Then $\hat C(a, v) = C(a, v)$ for every $a \in [0,1]$ and every $v \in \overline{\mathcal R}_\theta$.
--
--   With $\hat C$ the linearly interpolating copula of Proposition A.9, this shows that the copula $C$ of Theorem 2 coincides with it on $[0,1]\times\overline{\mathcal R}_\theta$, hence is linearly interpolating.
--
--   Differences from the source:
--   - encoding: "almost everywhere, $u \in [0,1]$", $\overline{\mathcal R}_\theta$ → `∀ᵐ` for Lebesgue measure restricted to $[0,1]$, `rbarTheta μ`; reason: Lean convention; same statement.
-- source:
--   Lo–Wu–Zhang–Zhao, Optimal Impact Portfolios with General Dependence and Marginals, SSRN 4177277 (draft of February 25, 2024), Appendix C.3, proof of Theorem 2, "only if", last paragraph, p.83 (PDF p.86)

import Mathlib
import Definitions.Def_ImpactCopula_IsCopulaOf
import Definitions.Def_ImpactCopula_mpdd
import Definitions.Def_ImpactCopula_rbarTheta

open MeasureTheory

namespace ImpactCopula

/-- **`C ≡ Ĉ` on `[0, 1] × R̄_θ`**, proof of Theorem 2, "only if", Lo–Wu–Zhang–Zhao, *Optimal Impact Portfolios with General Dependence and Marginals*, SSRN 4177277 (draft of February 25, 2024), p.83 (PDF p.86): if `C`
and `Ĉ` are copulas of `F` and, for any `y ∈ ℝ`, `D₁Ĉ(u, F_θ(y)) = D₁C(u, F_θ(y))` almost
everywhere, `u ∈ [0, 1]`, then `Ĉ(a, v) = C(a, v)` for all `a ∈ [0, 1]` and `v ∈ R̄_θ`.

**Formalization Note.** "Almost everywhere, u ∈ [0, 1]" is `∀ᵐ` with respect to Lebesgue
measure restricted to `[0, 1]`; `R̄_θ` is `rbarTheta μ`, the closure of the range of `F_θ`. -/
theorem copula_eq_on_rbar (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ] (C Chat : ℝ → ℝ → ℝ)
    (hC : IsCopulaOf C μ) (hChat : IsCopulaOf Chat μ)
    (h : ∀ y : ℝ, ∀ᵐ u ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      mpdd Chat u (cdfTheta μ y) = mpdd C u (cdfTheta μ y)) :
    ∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ v ∈ rbarTheta μ, Chat a v = C a v := by sorry

end ImpactCopula
