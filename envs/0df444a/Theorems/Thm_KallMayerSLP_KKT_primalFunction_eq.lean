-- Prove2me | Theorems.Thm_KallMayerSLP_KKT_primalFunction_eq
-- name    : KallMayerSLP.KKT.primalFunction_eq
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:10:19.988471+00:00
-- url     : https://prove2.me/theorems/b65e4189-262c-467d-9744-625632e9922c
-- title:
--   The primal problem $\min_x\sup_{u\ge0}L(x,u)$ is the program (3.1)
-- statement:
--   Throughout, $f:\mathbb R^n\to\mathbb R$ and $g_1,\dots,g_m:\mathbb R^n\to\mathbb R$ are convex and continuously differentiable, the book's standing assumptions for the program
--   $$
--   \min f(x)\quad\text{s.t.}\quad g_i(x)\le0,\ i=1,\dots,m,\tag{3.1}
--   $$
--   with feasible set $\mathcal B=\{x\mid g_i(x)\le 0,\ i=1,\dots,m\}$.
--
--   Let $L$ be the Lagrange function of (3.1). Then for every $x\in\mathbb R^n$
--   $$
--   \sup_{u\ge 0}L(x,u)=\begin{cases}f(x),&x\in\mathcal B,\\ +\infty,&x\notin\mathcal B,\end{cases}
--   $$
--   and consequently
--   $$
--   \inf_{x\in\mathbb R^n}\ \sup_{u\ge0}L(x,u)=\inf\{f(x)\mid g(x)\le 0\}.
--   $$
--
--   This is why $\min_x\sup_{u\ge0}L(x,u)$ is regarded as the primal problem and $\max_{u\ge0}\inf_xL(x,u)$ as its dual.
--
--   Differences from the source:
--   - encoding: ℝⁿ with zᵀv → EuclideanSpace ℝ (Fin n) with the inner product ⟪z, v⟫ and Mathlib's gradient; reason: Lean convention; the same space and the same gradient for differentiable functions
--   - reading: min_x sup_{u≥0} L(x, u) = min{f(x) | g(x) ≤ 0} → equality of infima in EReal; reason: the minima need not be attained (e.g. an empty feasible set), so min is read as inf, with +∞ allowed
--   - generalization: equality of the two optimal values → also the pointwise identity sup_{u≥0} L(x, u) = f(x) on 𝓑 and +∞ off 𝓑; reason: the pointwise identity is the content of 'by definition of L'; the second conjunct is the source's statement
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 1, §3.1, p.66 (PDF 77)

import Mathlib
import Definitions.Def_KallMayerSLP_KKT_primalFunction
import Definitions.Def_KallMayerSLP_KKT_feasibleSet

open Classical

namespace KallMayerSLP.KKT

/-- **The primal problem `min_x sup_{u≥0} L(x, u)` is the program (3.1).**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 1, §3.1, p.66 (PDF 77): "By definition of `L(·,·)` follows
`min_x sup_{u≥0} L(x, u) = min{f(x) | g(x) ≤ 0}`."

Here `f` and every `gᵢ` are convex on `ℝⁿ` and continuously differentiable (`ContDiff ℝ 1`), the
book's standing assumptions for (3.1) (p.61 and p.62). The statement has two conjuncts: pointwise, `sup_{u≥0} L(x, u)` is `f(x)` for
feasible `x` and `+∞` otherwise; and the two optimal values agree.

**Formalization Note.** Values are in `EReal` (`+∞` is `⊤`). The book's `min` is read as an
infimum (it need not be attained, e.g. for an empty feasible set both sides are `+∞`). -/
theorem primalFunction_eq {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (hg : ∀ i, ConvexOn ℝ Set.univ (g i))
    (hf1 : ContDiff ℝ 1 f) (hg1 : ∀ i, ContDiff ℝ 1 (g i)) :
    (∀ x, primalFunction f g x = if x ∈ feasibleSet g then ((f x : ℝ) : EReal) else ⊤) ∧
    ((⨅ x, primalFunction f g x) = ⨅ x ∈ feasibleSet g, ((f x : ℝ) : EReal)) := by sorry

end KallMayerSLP.KKT
