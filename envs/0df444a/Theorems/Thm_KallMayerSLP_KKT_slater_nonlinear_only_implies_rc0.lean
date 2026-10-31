-- Prove2me | Theorems.Thm_KallMayerSLP_KKT_slater_nonlinear_only_implies_rc0
-- name    : KallMayerSLP.KKT.slater_nonlinear_only_implies_rc0
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:11:18.776252+00:00
-- url     : https://prove2.me/theorems/5e1b3747-d957-418c-964d-a6cf39fa7e38
-- title:
--   Slater's condition is needed for the nonlinear constraints only
-- statement:
--   Throughout, $f:\mathbb R^n\to\mathbb R$ and $g_1,\dots,g_m:\mathbb R^n\to\mathbb R$ are convex and continuously differentiable, the book's standing assumptions for the program
--   $$
--   \min f(x)\quad\text{s.t.}\quad g_i(x)\le0,\ i=1,\dots,m,\tag{3.1}
--   $$
--   with feasible set $\mathcal B=\{x\mid g_i(x)\le 0,\ i=1,\dots,m\}$.
--
--   Let $L\subseteq\{1,\dots,m\}$ be a set of indices of linear constraints, $g_i(x)=b_i-a^{(i)\mathsf T}x$ for $i\in L$, and suppose there is a feasible point $\tilde x\in\mathcal B$ with
--   $$
--   g_i(\tilde x)<0\qquad\forall i\notin L .
--   $$
--   Then (3.1) satisfies the regularity condition RC 0.
--
--   With $L=\emptyset$ this is "RC 1 implies RC 0"; with all constraints linear it recovers Remark 3.1.
--
--   Differences from the source:
--   - encoding: ℝⁿ with zᵀv → EuclideanSpace ℝ (Fin n) with the inner product ⟪z, v⟫ and Mathlib's gradient; reason: Lean convention; the same space and the same gradient for differentiable functions
--   - reading: the Slater condition needs to be required for nonlinear constraints only → hypothesis: some feasible x̃ with gᵢ(x̃) < 0 for i ∉ L (L the linear constraints); conclusion RC 0; reason: the sentence qualifies the Slater condition in its role as a sufficient condition for RC 0, stated in the next sentence
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 1, §3, p.63 (PDF 74)

import Mathlib
import Definitions.Def_KallMayerSLP_KKT_RC0

open scoped RealInnerProductSpace

namespace KallMayerSLP.KKT

/-- **Slater's condition is needed for the nonlinear constraints only.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 1, §3, p.63 (PDF 74): "Similarly to Remark 3.1 the Slater condition needs to be required for
non-linear constraints only, whereas for linear constraints it may be abandonned. Without proof we
mention that, for convex problems, `RC 1` implies `RC 0`."

Here `f` and every `gᵢ` are convex on `ℝⁿ` and continuously differentiable (`ContDiff ℝ 1`), the
book's standing assumptions for (3.1) (p.61 and p.62). The constraints with index in `L` are linear, `gᵢ(x) = bᵢ − a⁽ⁱ⁾ᵀx`, and there
is a feasible point `x̃` with `gᵢ(x̃) < 0` for every `i ∉ L`. Then `RC 0` holds.

**Formalization Note.** The sentence is read, as its context says, as a statement about `RC 0`:
the Slater-type hypothesis implying `RC 0` may drop the strict inequality for the linear
constraints, which `x̃` only has to satisfy (feasibility). -/
theorem slater_nonlinear_only_implies_rc0 {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (hg : ∀ i, ConvexOn ℝ Set.univ (g i))
    (hf1 : ContDiff ℝ 1 f) (hg1 : ∀ i, ContDiff ℝ 1 (g i))
    (L : Finset (Fin m)) (a : Fin m → EuclideanSpace ℝ (Fin n)) (b : Fin m → ℝ)
    (hlin : ∀ i ∈ L, ∀ x, g i x = b i - ⟪a i, x⟫)
    (hS : ∃ x ∈ feasibleSet g, ∀ i ∉ L, g i x < 0) :
    RC0 f g := by sorry

end KallMayerSLP.KKT
