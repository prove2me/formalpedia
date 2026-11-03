-- Prove2me | Theorems.Thm_MonoInclCLC_lemma_2_1
-- name    : MonoInclCLC.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:19:58.319766+00:00
-- url     : https://prove2.me/theorems/3d06f5b5-2450-44f6-acd4-2960b332e5f4
-- title:
--   Lemma 2.1, p.4 — $\varphi(\lambda,\cdot)$ is $\lambda^{1/(p-1)}$-Lipschitz
-- statement:
--   Let $\mathcal H$ be a real Hilbert space and $A:\mathcal H\rightrightarrows\mathcal H$ a maximal monotone operator with $A^{-1}(0)=\{x:0\in Ax\}\neq\emptyset$. For an integer $p\ge 2$ let $\varphi(\lambda,x)=\lambda^{1/(p-1)}\|x-(I+\lambda A)^{-1}x\|$ for $\lambda>0$, and $\varphi(0,x)=0$. Then, for all $x_1,x_2\in\mathcal H$ and all $\lambda>0$,
--   $$
--   |\varphi(\lambda,x_1)-\varphi(\lambda,x_2)|\le\lambda^{\frac{1}{p-1}}\|x_1-x_2\|.
--   $$
--   This is the Lipschitz estimate in the state variable that later controls the feedback law along a trajectory.
--
--   Differences from the source:
--   - encoding: the resolvent (I + λA)⁻¹ as an operator determined by A → a family J with IsResolvent l A (J l) for every l > 0; reason: for maximal monotone A such a map exists (Minty) and is unique (monotonicity), so no instance changes
-- source:
--   Lin, Jordan, Monotone Inclusions, Acceleration and Closed-Loop Control, arXiv:2111.08093v4, Lemma 2.1, p.4

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_MonoInclCLC_phi

open InnerProductSpace ThreeOpSplitting.Convergence

namespace MonoInclCLC

/-- **Lemma 2.1** (Lin, Jordan, *Monotone Inclusions, Acceleration and Closed-Loop Control*, arXiv:2111.08093v4, Lemma 2.1, p.4): for `p ≥ 2`,
`|ϕ(λ, x₁) - ϕ(λ, x₂)| ≤ λ^(1/(p-1)) ‖x₁ - x₂‖` for all `x₁, x₂` and all `λ > 0`.

**Formalization Note.** `J l` is the resolvent `(I + l A)⁻¹` for `l > 0`. The standing assumptions of p.3 (`A` maximal monotone, `A⁻¹(0) ≠ ∅`) are hypotheses. -/
theorem lemma_2_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H → Set H) (hA : IsMaximalMonotone A) (hzer : (zer A).Nonempty)
    (J : ℝ → H → H) (hJ : ∀ l : ℝ, 0 < l → IsResolvent l A (J l))
    (p : ℕ) (hp : 2 ≤ p)
    (x₁ x₂ : H) (l : ℝ) (hl : 0 < l) :
    |phi J p l x₁ - phi J p l x₂| ≤ l ^ (1 / ((p : ℝ) - 1)) * ‖x₁ - x₂‖ := by sorry

end MonoInclCLC
