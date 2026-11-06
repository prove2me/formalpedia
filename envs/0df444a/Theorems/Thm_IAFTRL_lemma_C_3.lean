-- Prove2me | Theorems.Thm_IAFTRL_lemma_C_3
-- name    : IAFTRL.lemma_C_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:46:55.398202+00:00
-- url     : https://prove2.me/theorems/e3131ddc-cc65-446b-bdb2-f91180f95a6b
-- title:
--   Lemma C.3 — a finite feasible allocation of cost at most $2c^*$
-- statement:
--   Let $\mathcal A=\{a_1,\dots,a_K\}$ be a finite action set in the unit ball of $\mathbb R^d$ ($d\ge1$) spanning $\mathbb R^d$, let $\theta\in\mathbb R^d$ have a unique optimal action $a^*$, write $\Delta(a)=(a-a^*)^\top\theta$, and let $\Delta_0>0$ satisfy $\Delta_0\le\Delta(a)$ for every $a\ne a^*$. Then:
--   1. there is a feasible sampling allocation $n$ of (1.2) with
--   $$
--   c^n(\mathcal A,\theta)\le2c^*(\mathcal A,\theta),\qquad N_n\le\frac{4(d+G_{\mathcal A}^2)}{\Delta_0^2};
--   $$
--   2. $c^*(\mathcal A,\theta)\le 2d/\Delta_0$.
--
--   Here $c^*(\mathcal A,\theta)$ is the information-acquisition complexity (1.2), $c^n$ the cost and $N_n$ the total mass of $n$, and $G_{\mathcal A}$ the interpolation constant of Definition C.1. The allocation fixes the horizon-independent constant $M_{\mathcal A,\theta}=M_{n^\circ}$ in the proof of Theorem 2.1.
--
--   **Formalization Note** $c^*(\mathcal A,\theta)$ is the published `BanditAlgorithm.linearBanditAllocationValue arms (−θ)`: that definition is stated for rewards, so its gap at $-\theta$ is the loss gap $\Delta$, and under a unique minimizer its constraint index set "gap $>0$" is $\{a\ne a^*\}$.
--
--   Differences from the source:
--   - generalization: $\Delta_{\min}$ → any $\Delta_0$ with $0<\Delta_0\le\Delta(a)$ for all $a\ne a^*$; reason: at $\Delta_0=\Delta_{\min}$ this is the lemma; also covers $K=1$, where $\Delta_{\min}$ is undefined
--   - generalization: standing assumptions $\|\theta\|_{\mathcal A}\le1$ and $\Delta_{\min}\le1$ of Section 1.1 → not assumed; reason: the lemma and its proof do not use them; specializes to the source
--   - encoding: $c^*(\mathcal A,\theta)$ of (1.2) → `BanditAlgorithm.linearBanditAllocationValue arms (−θ)`; reason: same set of allocations and same objective under a unique minimizer (rewards convention, hence $-\theta$)
--   - encoding: $\mathbb R^d$ → $d\ge1$; reason: the paper works in $\mathbb R^d$ with a spanning action set in the unit ball
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299, Appendix C.2, Lemma C.3, p.60

import Mathlib
import Definitions.Def_LinearBanditProtocol
import Definitions.Def_IAFTRL_IsActionSet
import Definitions.Def_IAFTRL_IsUniqueMin
import Definitions.Def_IAFTRL_IsFeasibleAlloc
import Definitions.Def_IAFTRL_allocCost
import Definitions.Def_IAFTRL_allocMass
import Definitions.Def_IAFTRL_GA

namespace IAFTRL

open Matrix

/-- **Lemma C.3 (Finite mass at cost at most `2c*`).** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits*, arXiv:2611.01299, Lemma C.3, p.60: "There is a
finite feasible sampling allocation with `c^n ≤ 2c*`, `N_n ≤ 4(d + G_𝒜²)Δ_min^{−2}`. Also
`c* ≤ 2dΔ_min^{−1}`."

Let `𝒜 = {a_1, …, a_K}` be a finite action set in the unit ball of `ℝ^d` spanning `ℝ^d`, let `θ` have
a unique minimizing action `a* = a_{jstar}`, and let `0 < Δ₀ ≤ Δ(a) = (a − a*)^⊤θ` for all `a ≠ a*`.
Then:
1. there is a feasible sampling allocation `n` (in the sense of (1.2)) with
   `c^n(𝒜, θ) ≤ 2c*(𝒜, θ)` and total mass `N_n ≤ 4(d + G_𝒜²)/Δ₀²`;
2. `c*(𝒜, θ) ≤ 2d/Δ₀`.

Here `c*(𝒜, θ)` is the information-acquisition complexity (1.2) and `G_𝒜` the interpolation constant
of Definition C.1.

**Formalization Note.** `c*(𝒜, θ)` is the published `BanditAlgorithm.linearBanditAllocationValue arms
(−θ)`: that bundle uses rewards, so its gap at `−θ` is the paper's loss gap, and under a unique
minimizer its constraint set "gap > 0" is `a ≠ a*`. `Δ₀` is any positive lower bound on the gaps; at
`Δ₀ = Δ_min` this is the lemma. "Finite" is automatic for a finite action set. -/
theorem lemma_C_3 {d K : ℕ} (hd : 1 ≤ d) (arms : Fin K → Fin d → ℝ) (hA : IsActionSet arms)
    (θ : Fin d → ℝ) (jstar : Fin K) (hu : IsUniqueMin arms θ jstar) (Δ₀ : ℝ) (hΔ₀ : 0 < Δ₀)
    (hΔ : ∀ j, j ≠ jstar → Δ₀ ≤ (arms j - arms jstar) ⬝ᵥ θ) :
    (∃ n : Fin K → ℝ, IsFeasibleAlloc arms θ jstar n ∧
      allocCost arms θ jstar n ≤ 2 * BanditAlgorithm.linearBanditAllocationValue arms (-θ) ∧
      allocMass n ≤ 4 * ((d : ℝ) + GA arms ^ 2) / Δ₀ ^ 2) ∧
    BanditAlgorithm.linearBanditAllocationValue arms (-θ) ≤ 2 * (d : ℝ) / Δ₀ := by sorry

end IAFTRL
