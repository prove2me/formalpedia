-- Prove2me | Theorems.Thm_KallMayerSLP_KKT_kkt_isSaddlePoint
-- name    : KallMayerSLP.KKT.kkt_isSaddlePoint
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:10:13.040989+00:00
-- url     : https://prove2.me/theorems/7ecc6ff5-8f1d-49c9-bf1a-4b73edb658e2
-- title:
--   A KKT point is a saddle point of the Lagrange function (3.6)
-- statement:
--   Throughout, $f:\mathbb R^n\to\mathbb R$ and $g_1,\dots,g_m:\mathbb R^n\to\mathbb R$ are convex and continuously differentiable, the book's standing assumptions for the program
--   $$
--   \min f(x)\quad\text{s.t.}\quad g_i(x)\le0,\ i=1,\dots,m,\tag{3.1}
--   $$
--   with feasible set $\mathcal B=\{x\mid g_i(x)\le 0,\ i=1,\dots,m\}$.
--
--   Let $L(x,u)=f(x)+\sum_{i=1}^m u_ig_i(x)$ be the Lagrange function. If $(\hat x,\hat u)$ satisfies the KKT conditions (3.3), then $(\hat x,\hat u\ge0)$ is a saddle point of $L$:
--   $$
--   L(\hat x,u)\le L(\hat x,\hat u)\le L(x,\hat u)\qquad\forall u\ge 0,\ \forall x\in\mathbb R^n.\tag{3.6}
--   $$
--
--   This links the KKT conditions to the saddle point theorem, Proposition 3.5.
--
--   Differences from the source:
--   - encoding: ℝⁿ with zᵀv → EuclideanSpace ℝ (Fin n) with the inner product ⟪z, v⟫ and Mathlib's gradient; reason: Lean convention; the same space and the same gradient for differentiable functions
--   - generalization: the KKT point (x̂, û ≥ 0) of Proposition 3.4 (whose hypothesis includes the Slater condition RC 1) → any (x̂, û) satisfying (3.3), without RC 1; reason: the derivation on pp.65–66 uses only (3.3) and convexity; with RC 1 added it is the source's statement
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 1, §3.1, eq. (3.6), pp.65–66 (PDF 76–77)

import Mathlib
import Definitions.Def_KallMayerSLP_KKT_IsKKT
import Definitions.Def_KallMayerSLP_KKT_IsSaddlePoint

namespace KallMayerSLP.KKT

/-- **A KKT point is a saddle point of the Lagrange function (3.6).**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 1, §3.1, eq. (3.6), p.66 (PDF 77): "Hence, the KKT point `(x̂, û ≥ 0)` of Proposition 3.4 is a
saddle point of the Lagrange function: `L(x̂, u) ≤ L(x̂, û) ≤ L(x, û) ∀u ≥ 0, ∀x ∈ ℝⁿ`."

Here `f` and every `gᵢ` are convex on `ℝⁿ` and continuously differentiable (`ContDiff ℝ 1`), the
book's standing assumptions for (3.1) (p.61 and p.62), and `(x̂, û)` satisfies the KKT conditions (3.3).

**Formalization Note.** "The KKT point of Proposition 3.4" is any pair satisfying (3.3); the
derivation on pp.65–66 uses (3.3) and convexity only, not the Slater condition, which is
therefore not a hypothesis. -/
theorem kkt_isSaddlePoint {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (hg : ∀ i, ConvexOn ℝ Set.univ (g i))
    (hf1 : ContDiff ℝ 1 f) (hg1 : ∀ i, ContDiff ℝ 1 (g i))
    (xh : EuclideanSpace ℝ (Fin n)) (uh : Fin m → ℝ) (h : IsKKT f g xh uh) :
    IsSaddlePoint f g xh uh := by sorry

end KallMayerSLP.KKT
