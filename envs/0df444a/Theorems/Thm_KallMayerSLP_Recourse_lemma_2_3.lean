-- Prove2me | Theorems.Thm_KallMayerSLP_Recourse_lemma_2_3
-- name    : KallMayerSLP.Recourse.lemma_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:11:54.664595+00:00
-- url     : https://prove2.me/theorems/6d8bf07c-3b0b-4546-a3a7-e7d851b132a8
-- title:
--   Lemma 2.3 — the subdifferential of an LP value function is the set of optimal dual solutions
-- statement:
--   Let $A\in\mathbb R^{m\times n}$, $c\in\mathbb R^n$, and assume that the linear program
--
--   $$
--   \min\{c^{\mathsf T}x\mid Ax=b,\ x\ge 0\}
--   $$
--
--   is solvable for every right-hand side $b\in\mathbb R^m$. Let $\varphi(b)$ be its optimal value. Then $\varphi$ is convex on $\mathbb R^m$, it is subdifferentiable at every $b$, and its subdifferential is the set of optimal dual solutions at $b$:
--
--   $$
--   \partial\varphi(b)=\operatorname*{arg\,max}\{b^{\mathsf T}u\mid A^{\mathsf T}u\le c\}\qquad\text{for every }b\in\mathbb R^m .
--   $$
--
--   Here $g\in\partial\varphi(b)$ means $g^{\mathsf T}(z-b)\le\varphi(z)-\varphi(b)$ for all $z$. Applied to the recourse LP, this lemma yields the subdifferential formula of Theorem 2.2.
--
--   **Formalization Note** $\varphi$ is the published `KallMayer.Recourse.LPValue` (an `EReal` infimum, finite here by solvability), "solvable ∀b" is `KallMayer.Recourse.SolvableEveryRHS`, the argmax set is `KallMayer.Recourse.DualOptimizers`, and $\partial$ is the published `StochasticProg.RecourseKKT.subdifferential`.
--
--   Differences from the source:
--   - encoding: subdifferential of a convex function ℝⁿ → ℝ (Chapter 1, Def. 3.2, p.61); 'subdifferentiable at b' → the published `StochasticProg.RecourseKKT.subdifferential` of the `EReal` function (requires the value at the point to be finite); nonempty subdifferential; reason: the functions are finite here, where the two notions agree
--   - encoding: the optimal value φ(b) and '(obviously convex in b)' → `LPValue A c b` (`EReal`); convexity stated for its real part as the first conjunct; reason: φ is finite for every b by the solvability hypothesis
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, Lemma 2.3, p.206 (PDF 215); subgradient: Chapter 1, Def. 3.2, p.61

import Mathlib
import Definitions.Def_KallMayer_Recourse_LPValue
import Definitions.Def_StochasticProg_RecourseKKT_subdifferential

open KallMayer.Recourse (LPValue SolvableEveryRHS DualOptimizers)
open StochasticProg.RecourseKKT (subdifferential)
open Matrix

namespace KallMayerSLP.Recourse

/-- Lemma 2.3 (Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, Lemma 2.3, p.206,
PDF 215): assume that the LP `min{cᵀx | Ax = b, x ≥ 0}` is solvable `∀ b ∈ ℝᵐ`. Then its optimal value
`φ(b)` (obviously convex in `b`) is subdifferentiable at any `b`, and the subdifferential is given as
`∂φ(b) = argmax{bᵀu | Aᵀu ≤ c}`, the set of optimal dual solutions at `b`.

**Formalization Note.** `φ = KallMayer.Recourse.LPValue A c` (an `EReal` infimum), "solvable ∀b" is
`KallMayer.Recourse.SolvableEveryRHS A c`, and the argmax set is `KallMayer.Recourse.DualOptimizers`,
all published. The subdifferential is the published `StochasticProg.RecourseKKT.subdifferential`
(`g ∈ ∂φ(b)` iff `φ(b)` is a real number and `gᵀ(z − b) ≤ φ(z) − φ(b)` for all `z`), which is
Chapter 1, Def. 3.2 (p.61) for the real-valued `φ` of this lemma. The parenthetical convexity claim
is the first conjunct, for the real function `b ↦ φ(b)`. -/
theorem lemma_2_3 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ)
    (hsolv : SolvableEveryRHS A c) :
    ConvexOn ℝ Set.univ (fun b : Fin m → ℝ => (LPValue A c b).toReal) ∧
    ∀ b : Fin m → ℝ, (subdifferential (LPValue A c) b).Nonempty ∧
      subdifferential (LPValue A c) b = DualOptimizers A c b := by sorry

end KallMayerSLP.Recourse
