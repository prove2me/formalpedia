-- Prove2me | Theorems.Thm_KallMayerSLP_KKT_remark_3_1_linear
-- name    : KallMayerSLP.KKT.remark_3_1_linear
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:11:21.983098+00:00
-- url     : https://prove2.me/theorems/97c8f794-190d-46d4-a014-c33f92e7271c
-- title:
--   Remark 3.1 — linear constraints always satisfy RC 0
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be convex and continuously differentiable, and let all constraints of (3.1) be linear,
--   $$
--   g_i(x)=b_i-a^{(i)\mathsf T}x,\qquad i=1,\dots,m,
--   $$
--   with $a^{(i)}\in\mathbb R^n$, $b_i\in\mathbb R$. Then the program (3.1) satisfies the regularity condition RC 0.
--
--   So for linear constraints no further constraint qualification is needed for the KKT conditions.
--
--   Differences from the source:
--   - encoding: ℝⁿ with zᵀv → EuclideanSpace ℝ (Fin n) with the inner product ⟪z, v⟫ and Mathlib's gradient; reason: Lean convention; the same space and the same gradient for differentiable functions
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 1, §3, Remark 3.1, p.63 (PDF 74)

import Mathlib
import Definitions.Def_KallMayerSLP_KKT_RC0

open scoped RealInnerProductSpace

namespace KallMayerSLP.KKT

/-- **Remark 3.1 (first part): linear constraints satisfy `RC 0`.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 1, Remark 3.1, p.63 (PDF 74): "Observe that for linear constraints the regularity condition is
always satisfied: Having `gᵢ(x̂) = bᵢ − a⁽ⁱ⁾ᵀx̂ = 0 ∀i ∈ I(x̂)` implies … `RC 0` is satisfied."

Here `f` is convex and continuously differentiable (standing assumptions, pp.61–62) and every
constraint is linear (affine), `gᵢ(x) = bᵢ − a⁽ⁱ⁾ᵀx`.

**Formalization Note.** `a⁽ⁱ⁾ᵀx` is `⟪a i, x⟫`; the linear constraint functions are convex and
smooth, so the standing assumptions on the `gᵢ` hold automatically. -/
theorem remark_3_1_linear {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (hf1 : ContDiff ℝ 1 f)
    (a : Fin m → EuclideanSpace ℝ (Fin n)) (b : Fin m → ℝ)
    (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (hg : ∀ i x, g i x = b i - ⟪a i, x⟫) :
    RC0 f g := by sorry

end KallMayerSLP.KKT
