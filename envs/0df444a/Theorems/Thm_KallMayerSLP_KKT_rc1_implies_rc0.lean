-- Prove2me | Theorems.Thm_KallMayerSLP_KKT_rc1_implies_rc0
-- name    : KallMayerSLP.KKT.rc1_implies_rc0
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:11:10.220851+00:00
-- url     : https://prove2.me/theorems/5894a74f-cdc0-4dda-becf-9e3683b0d8fc
-- title:
--   For convex problems the Slater condition RC 1 implies RC 0
-- statement:
--   Throughout, $f:\mathbb R^n\to\mathbb R$ and $g_1,\dots,g_m:\mathbb R^n\to\mathbb R$ are convex and continuously differentiable, the book's standing assumptions for the program
--   $$
--   \min f(x)\quad\text{s.t.}\quad g_i(x)\le0,\ i=1,\dots,m,\tag{3.1}
--   $$
--   with feasible set $\mathcal B=\{x\mid g_i(x)\le 0,\ i=1,\dots,m\}$.
--
--   If (3.1) satisfies the Slater condition RC 1 (a feasible $\tilde x$ with $g_i(\tilde x)<0$ for all $i$), then it satisfies the regularity condition RC 0.
--
--   This is the step that makes Proposition 3.4 a consequence of the Farkas lemma.
--
--   Differences from the source:
--   - encoding: ℝⁿ with zᵀv → EuclideanSpace ℝ (Fin n) with the inner product ⟪z, v⟫ and Mathlib's gradient; reason: Lean convention; the same space and the same gradient for differentiable functions
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 1, §3, p.63 (PDF 74)

import Mathlib
import Definitions.Def_KallMayerSLP_KKT_RC0
import Definitions.Def_KallMayerSLP_KKT_RC1

namespace KallMayerSLP.KKT

/-- **For convex problems, `RC 1` (Slater) implies `RC 0`.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 1, §3, p.63 (PDF 74): "Without proof we mention that, for convex problems, `RC 1` implies
`RC 0`."

Here `f` and every `gᵢ` are convex on `ℝⁿ` and continuously differentiable (`ContDiff ℝ 1`), the
book's standing assumptions for (3.1) (p.61 and p.62). -/
theorem rc1_implies_rc0 {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (hg : ∀ i, ConvexOn ℝ Set.univ (g i))
    (hf1 : ContDiff ℝ 1 f) (hg1 : ∀ i, ContDiff ℝ 1 (g i)) (hS : RC1 g) :
    RC0 f g := by sorry

end KallMayerSLP.KKT
