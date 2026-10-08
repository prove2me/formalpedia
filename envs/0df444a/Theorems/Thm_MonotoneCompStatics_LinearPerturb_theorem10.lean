-- Prove2me | Theorems.Thm_MonotoneCompStatics_LinearPerturb_theorem10
-- name    : MonotoneCompStatics.LinearPerturb.theorem10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:14:49.932848+00:00
-- url     : https://prove2.me/theorems/c12b11eb-529d-4ddc-acad-ee83b858f056
-- title:
--   Theorem 10 — f + p·x (resp. f − w·x, w ≥ 0, f nondecreasing) is quasisupermodular with single crossing for all prices iff f is supermodular
-- statement:
--   Let $n \ge 0$ and $f : \mathbb{R}^n \times \mathbb{R} \to \mathbb{R}$, $(x, t) \mapsto f(x, t)$. Order $\mathbb{R}^n$ componentwise and $\mathbb{R}^n \times \mathbb{R}$ by the product order; joins $\vee$ and meets $\wedge$ are componentwise maxima and minima. Write $p \cdot x = \sum_i p_i x_i$. Say that $f$ is **supermodular** if
--
--   $$
--   f(z) + f(z') \le f(z \vee z') + f(z \wedge z') \qquad \text{for all } z, z' \in \mathbb{R}^n \times \mathbb{R}.
--   $$
--
--   1. $f(x, t) + p \cdot x$ is quasisupermodular in $x$ and has the single crossing property in $(x; t)$ for all $p \in \mathbb{R}^n$ if and only if $f$ is supermodular.
--   2. If $f$ is nondecreasing in $x$ (for every fixed $t$), then $f(x, t) - w \cdot x$ is quasisupermodular in $x$ and has the single crossing property in $(x; t)$ for all nonnegative $w \in \mathbb{R}^n$ if and only if $f$ is supermodular.
--
--   In the economic reading, $x$ is a vector of activity levels, $t$ a parameter, $p$ a vector of prices (or $w$ a vector of nonnegative input costs) that enter linearly. Supermodularity is never necessary for the argmax to be monotone, but by this theorem it is exactly the condition under which the ordinal conditions of the Monotonicity Theorem survive every such linear price term.
--
--   **Formalization Note** $f$ is curried, `f : (Fin n → ℝ) → ℝ → ℝ`; $\mathbb{R}^n$ is `Fin n → ℝ` with Mathlib's pointwise order, $p \cdot x$ is `p ⬝ᵥ x`. "$f$ is supermodular" is read jointly in $(x, t)$ on the product lattice (the published `SupermodularOn` with `Set.univ`), as the paper's proof confirms. "Quasisupermodular in $x$" means for every fixed $t$. "Nondecreasing in $x$" is `Monotone (fun x => f x t)` for every $t$, a hypothesis of the second equivalence only; "nonnegative $w$" is `0 ≤ w` componentwise. The second statement uses $- w\cdot x$ with $w \ge 0$, not $+p\cdot x$.
-- source:
--   Milgrom and Shannon, Monotone Comparative Statics, Econometrica 62 (1994), p. 166 (PDF p. 11), Theorem 10

import Mathlib
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn
import Definitions.Def_MonotoneCompStatics_Monotonicity_QuasiSupermodularOn
import Definitions.Def_MonotoneCompStatics_Monotonicity_SingleCrossing

namespace MonotoneCompStatics.LinearPerturb

/-- Milgrom and Shannon (1994), p. 166, Theorem 10. Let `f : ℝⁿ × ℝ → ℝ` (curried).
(1) `f(x, t) + p · x` is quasisupermodular in `x` and has the single crossing property in
`(x; t)` for all `p ∈ ℝⁿ` iff `f` is supermodular (jointly in `(x, t)` on `ℝⁿ × ℝ`).
(2) If `f` is nondecreasing in `x`, then `f(x, t) − w · x` is quasisupermodular in `x` and has the
single crossing property in `(x; t)` for all nonnegative `w ∈ ℝⁿ` iff `f` is supermodular. -/
theorem theorem10 {n : ℕ} (f : (Fin n → ℝ) → ℝ → ℝ) :
    ((∀ p : Fin n → ℝ, (∀ t, MonotoneCompStatics.Monotonicity.QuasiSupermodularOn (fun x => f x t + p ⬝ᵥ x) Set.univ) ∧
        MonotoneCompStatics.Monotonicity.SingleCrossing (fun x t => f x t + p ⬝ᵥ x)) ↔
      Supermodularity.Monotonicity.SupermodularOn
        (fun z : (Fin n → ℝ) × ℝ => f z.1 z.2) Set.univ) ∧
    ((∀ t, Monotone (fun x => f x t)) →
      ((∀ w : Fin n → ℝ, 0 ≤ w →
          (∀ t, MonotoneCompStatics.Monotonicity.QuasiSupermodularOn (fun x => f x t - w ⬝ᵥ x) Set.univ) ∧
          MonotoneCompStatics.Monotonicity.SingleCrossing (fun x t => f x t - w ⬝ᵥ x)) ↔
        Supermodularity.Monotonicity.SupermodularOn
          (fun z : (Fin n → ℝ) × ℝ => f z.1 z.2) Set.univ)) := by sorry

end MonotoneCompStatics.LinearPerturb
