-- Prove2me | Theorems.Thm_IAFTRL_lemma_C_3_allocation
-- name    : IAFTRL.lemma_C_3_allocation
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-15T08:05:46.908816+00:00
-- url     : https://prove2.me/theorems/5025a2b3-d96f-48ea-b429-a78b6ebafe1c
-- title:
--   Lemma C.3 (first claim) — a feasible allocation of cost at most $2c^*$ and bounded mass
-- statement:
--   Let $\mathcal A=\{a_1,\dots,a_K\}$ be a finite action set in the Euclidean unit ball of $\mathbb R^d$ ($d\ge1$) that spans $\mathbb R^d$. Let $\theta\in\mathbb R^d$ have a unique minimizing action $a^*$, write $\Delta(a)=(a-a^*)^\top\theta$ for the loss gap, and let $0<\Delta_0\le\Delta(a)$ for every $a\ne a^*$.
--
--   Then there is a feasible sampling allocation $n\in\mathbb R_{\ge0}^{\mathcal A}$ in the sense of (1.2) — $H_n=\sum_a n_a aa^\top\succ0$ and $\|a\|^2_{H_n^{-1}}\le\Delta(a)^2/2$ for all $a\ne a^*$ — such that
--   $$
--   c^n(\mathcal A,\theta)\le 2\,c^*(\mathcal A,\theta)\qquad\text{and}\qquad N_n=\sum_a n_a\le\frac{4\,(d+G_{\mathcal A}^2)}{\Delta_0^2}.
--   $$
--   Here $c^n(\mathcal A,\theta)=\sum_a n_a\Delta(a)$ is the information-acquisition cost of $n$, $c^*(\mathcal A,\theta)$ is its infimum over feasible allocations (1.2), and $G_{\mathcal A}$ is the interpolation constant of Definition C.1.
--
--   Since $c^*$ is an infimum that need not be attained, this is the allocation $n^\circ$ at which Theorem 2.1 applies the fixed-allocation bound of Proposition 2.1.
--
--   **Formalization Note** This is the first conjunct of `IAFTRL.lemma_C_3`, with the same hypotheses; $c^*(\mathcal A,\theta)$ is `BanditAlgorithm.linearBanditAllocationValue arms (−θ)` (rewards convention).
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299, Lemma C.3, p.60 (first sentence)

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

/-- **Lemma C.3, first claim (a finite feasible allocation of cost at most `2c*`).** Zhao–Tan,
*Best-of-Both-Worlds FTRL for Linear Bandits*, arXiv:2611.01299, Lemma C.3, p.60: "There is a
finite feasible sampling allocation with `c^n ≤ 2c*`, `N_n ≤ 4(d + G_𝒜²)Δ_min^{−2}`."

Same setting as `IAFTRL.lemma_C_3`: `𝒜 = {a_1, …, a_K}` a finite action set in the unit ball of `ℝ^d`
spanning `ℝ^d`, `θ` with a unique minimizing action `a* = a_{jstar}`, and `0 < Δ₀ ≤ Δ(a)` for all
`a ≠ a*`. There is a feasible sampling allocation `n` (in the sense of (1.2)) with
`c^n(𝒜, θ) ≤ 2c*(𝒜, θ)` and total mass `N_n ≤ 4(d + G_𝒜²)/Δ₀²`.

**Formalization Note.** The first conjunct of `IAFTRL.lemma_C_3`, with the same hypotheses and
conventions (`c*` is `BanditAlgorithm.linearBanditAllocationValue arms (−θ)`). -/
theorem lemma_C_3_allocation {d K : ℕ} (hd : 1 ≤ d) (arms : Fin K → Fin d → ℝ) (hA : IsActionSet arms)
    (θ : Fin d → ℝ) (jstar : Fin K) (hu : IsUniqueMin arms θ jstar) (Δ₀ : ℝ) (hΔ₀ : 0 < Δ₀)
    (hΔ : ∀ j, j ≠ jstar → Δ₀ ≤ (arms j - arms jstar) ⬝ᵥ θ) :
    ∃ n : Fin K → ℝ, IsFeasibleAlloc arms θ jstar n ∧
      allocCost arms θ jstar n ≤ 2 * BanditAlgorithm.linearBanditAllocationValue arms (-θ) ∧
      allocMass n ≤ 4 * ((d : ℝ) + GA arms ^ 2) / Δ₀ ^ 2 := by sorry

end IAFTRL
