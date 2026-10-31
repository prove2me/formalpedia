-- Prove2me | Theorems.Thm_KallMayerSLP_KKT_necessary_condition_strict
-- name    : KallMayerSLP.KKT.necessary_condition_strict
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:10:12.587809+00:00
-- url     : https://prove2.me/theorems/a86214aa-3515-4613-9265-4e62a925b883
-- title:
--   Necessary optimality condition: no strictly descent-feasible direction at an optimum of (3.1)
-- statement:
--   Throughout, $f:\mathbb R^n\to\mathbb R$ and $g_1,\dots,g_m:\mathbb R^n\to\mathbb R$ are convex and continuously differentiable, the book's standing assumptions for the program
--   $$
--   \min f(x)\quad\text{s.t.}\quad g_i(x)\le0,\ i=1,\dots,m,\tag{3.1}
--   $$
--   with feasible set $\mathcal B=\{x\mid g_i(x)\le 0,\ i=1,\dots,m\}$.
--
--   Let $\hat x$ be an optimal solution of (3.1) and $I(\hat x)=\{i\mid g_i(\hat x)=0\}$ its active set. Then for every $z\in\mathbb R^n$,
--   $$
--   z^{\mathsf T}\nabla g_i(\hat x)<0\quad\forall i\in I(\hat x)\qquad\Longrightarrow\qquad z^{\mathsf T}\nabla f(\hat x)\ge 0 .
--   $$
--
--   This is the condition from which the regularity condition RC 0 is obtained by relaxing the strict inequalities.
--
--   Differences from the source:
--   - encoding: ℝⁿ with zᵀv → EuclideanSpace ℝ (Fin n) with the inner product ⟪z, v⟫ and Mathlib's gradient; reason: Lean convention; the same space and the same gradient for differentiable functions
--   - reading: zᵀ∇gᵢ(x̂) < 0, i ∈ I(x̂) → ∀ i ∈ activeSet g x̂, ⟪z, ∇gᵢ(x̂)⟫ < 0; reason: the sentence before it writes the same hypothesis as ∀i ∈ I(x̂)
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 1, §3, pp.62–63 (PDF 73–74)

import Mathlib
import Definitions.Def_KallMayerSLP_KKT_IsOptimal
import Definitions.Def_KallMayerSLP_KKT_activeSet

open scoped RealInnerProductSpace

namespace KallMayerSLP.KKT

/-- **Necessary condition for an optimum of (3.1), strict form.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 1, §3, pp.62–63 (PDF 73–74): "For `x̂` to be a solution of (3.1) we have therefore the
(necessary) condition `zᵀ∇gᵢ(x̂) < 0, i ∈ I(x̂)` implies that `zᵀ∇f(x̂) ≥ 0`."

Here `f` and every `gᵢ` are convex on `ℝⁿ` and continuously differentiable (`ContDiff ℝ 1`), the
book's standing assumptions for (3.1) (p.61 and p.62); `x̂` is an optimal solution of (3.1) and `I(x̂)` its active set.

**Formalization Note.** "`zᵀ∇gᵢ(x̂) < 0, i ∈ I(x̂)`" is read as "for all `i ∈ I(x̂)`", as in the
sentence before it ("`z̃ᵀ∇gᵢ(x̂) < 0 ∀i ∈ I(x̂)`"); `z` ranges over all of `ℝⁿ`. -/
theorem necessary_condition_strict {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (hg : ∀ i, ConvexOn ℝ Set.univ (g i))
    (hf1 : ContDiff ℝ 1 f) (hg1 : ∀ i, ContDiff ℝ 1 (g i))
    (xh : EuclideanSpace ℝ (Fin n)) (hxh : IsOptimal f g xh) :
    ∀ z : EuclideanSpace ℝ (Fin n),
      (∀ i ∈ activeSet g xh, ⟪z, gradient (g i) xh⟫ < 0) → 0 ≤ ⟪z, gradient f xh⟫ := by sorry

end KallMayerSLP.KKT
