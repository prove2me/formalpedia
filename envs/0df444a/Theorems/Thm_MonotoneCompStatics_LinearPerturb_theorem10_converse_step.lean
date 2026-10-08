-- Prove2me | Theorems.Thm_MonotoneCompStatics_LinearPerturb_theorem10_converse_step
-- name    : MonotoneCompStatics.LinearPerturb.theorem10_converse_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:14:21.501962+00:00
-- url     : https://prove2.me/theorems/fa078a71-e828-4d01-9466-5512f6ed7610
-- title:
--   Theorem 10, proof (converse step) — quasisupermodularity of g + p·x for every p forces supermodularity of g
-- statement:
--   Let $n \ge 0$ and give $\mathbb{R}^n$ the componentwise order, so that $x \vee y$ and $x \wedge y$ are the componentwise maximum and minimum. Let $g : \mathbb{R}^n \to \mathbb{R}$, and for a price vector $p \in \mathbb{R}^n$ write $p \cdot x = \sum_i p_i x_i$. If for **every** $p \in \mathbb{R}^n$ the function
--
--   $$
--   x \longmapsto g(x) + p \cdot x
--   $$
--
--   is quasisupermodular on $\mathbb{R}^n$, then $g$ is supermodular on $\mathbb{R}^n$:
--
--   $$
--   g(x) + g(y) \le g(x \vee y) + g(x \wedge y) \qquad \text{for all } x, y \in \mathbb{R}^n.
--   $$
--
--   This is the step of the proof of Theorem 10 that recovers supermodularity in $x$ (for a fixed value of the parameter $t$, which the paper suppresses) from quasisupermodularity of all linear perturbations. It shows that quasisupermodularity, although an ordinal property, pins down the cardinal property supermodularity once it is required robustly against all linear price terms.
--
--   **Formalization Note** $\mathbb{R}^n$ is `Fin n → ℝ` with Mathlib's pointwise order and lattice operations, and $p \cdot x$ is `p ⬝ᵥ x` (`dotProduct`). The hypothesis quantifies over all $p$, not over some $p$.
-- source:
--   Milgrom and Shannon, Monotone Comparative Statics, Econometrica 62 (1994), p. 166 (PDF p. 11), Theorem 10, proof (converse step)

import Mathlib
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn
import Definitions.Def_MonotoneCompStatics_Monotonicity_QuasiSupermodularOn

namespace MonotoneCompStatics.LinearPerturb

/-- Milgrom and Shannon (1994), p. 166, proof of Theorem 10 (the step for `x`, with `t`
suppressed): if `g + p · x` is quasisupermodular on `ℝⁿ` for every price vector `p ∈ ℝⁿ`, then
`g` is supermodular on `ℝⁿ` (componentwise order, meet and join). -/
theorem theorem10_converse_step {n : ℕ} (g : (Fin n → ℝ) → ℝ)
    (h : ∀ p : Fin n → ℝ, MonotoneCompStatics.Monotonicity.QuasiSupermodularOn (fun x => g x + p ⬝ᵥ x) Set.univ) :
    Supermodularity.Monotonicity.SupermodularOn g Set.univ := by sorry

end MonotoneCompStatics.LinearPerturb
