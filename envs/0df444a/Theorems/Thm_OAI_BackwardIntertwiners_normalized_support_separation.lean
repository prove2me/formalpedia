-- Prove2me | Theorems.Thm_OAI_BackwardIntertwiners_normalized_support_separation
-- name    : OAI.BackwardIntertwiners.normalized_support_separation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:23:59.444402+00:00
-- url     : https://prove2.me/theorems/51c1107c-0df5-4707-9ae8-361c798c6909
-- title:
--   Support separation for normalized weights with convex logarithmic profiles and quadratic rate above $\log 3$
-- statement:
--   Let $w:\mathbb{Z}\to\mathbb{R}$ be a two-sided weight sequence and, for $n\in\mathbb{N}=\{0,1,2,\dots\}$, put $P(n)=\log w(-n)$ and $Q(n)=-\log w(n)$; thus $P$ measures the growth of $w$ to the left and $Q$ its decay to the right. A function $F:\mathbb{N}\to\mathbb{R}$ is called *discretely convex* if its increments $F(n+1)-F(n)$ form a nondecreasing sequence.
--
--   We say that $w$ has the **support separation property** if the following holds for all sequences $b,c:\mathbb{Z}\to\mathbb{C}$: if neither $b$ nor $c$ is identically zero, if $|b_j|\le w(j)$ and $|c_j|\,w(j)\le 1$ for every $j\in\mathbb{Z}$, and if
--   $$\sum_{j\in\mathbb{Z}} b_j\,c_{j-r}=0\qquad\text{for every integer } r\ge 1,$$
--   then there are integers $t$ and $h$ such that
--   $$b_t\neq 0,\qquad c_h\neq 0,\qquad b_j=0\ \text{ for all } j>t,\qquad c_j=0\ \text{ for all } j<h,\qquad t\le h .$$
--   In words: the support of $b$ has a largest element $t$, the support of $c$ has a smallest element $h$, and every index in the support of $b$ is at most every index in the support of $c$.
--
--   **Theorem.** Assume that $w(j)>0$ for all $j\in\mathbb{Z}$, that $w$ is nonincreasing on $\mathbb{Z}$, that $w(0)=1$, and that $P$ and $Q$ are discretely convex. Assume further that there are real numbers $\lambda,\delta$ with $\log 3<\lambda<\delta$ such that
--   $$\delta n^2\le P(n)\qquad\text{and}\qquad \delta n^2\le Q(n)\qquad\text{for all sufficiently large } n\in\mathbb{N}.$$
--   Then $w$ has the support separation property. (The auxiliary number $\lambda$ only enters through the resulting requirement $\delta>\log 3$.)
--
--   So $w$ grows at least like $e^{\delta n^2}$ to the left and decays at least like $e^{-\delta n^2}$ to the right, with convex logarithmic profiles $P$ and $Q$. The theorem says that a sequence $b$ dominated by $w$ and a sequence $c$ dominated by $1/w$ whose one-sided correlations all vanish must have ordered, one-sided supports. It is the analytic core of the support-separation argument for weighted shifts in this development: after normalizing $w(0)=1$ it applies to every weight with an exact quadratic log-growth rate above $\log 3$, and through that to orthogonality relations between a vector and the forward orbit of another vector under a bilateral weighted shift.
--
--   **Formalization Note** The sums are Lean's unconditional sums `∑' j : ℤ`, which by convention equal $0$ when the family is not summable. Here `negativeLog w n = Real.log (w (-n))`, `positiveLog w n = -Real.log (w n)`, `DiscreteConvex F` means that `fun n => F (n+1) - F n` is monotone, "for all sufficiently large $n$" is `∀ᶠ n : ℕ in atTop`, and the conclusion is the predicate `SupportSeparation w`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BackwardIntertwiners/WeightSeparation.lean#L89-L167

import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvolutionBounds
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_CoefficientSupport
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_WeightSeparation

open OAI OAI.BackwardIntertwiners
open Filter
open scoped Topology

theorem OAI.BackwardIntertwiners.normalized_support_separation {w : ℤ → ℝ} (hw : ∀ j, 0 < w j)
    (hdec : Antitone w) (hw0 : w 0 = 1)
    (hP : DiscreteConvex (negativeLog w)) (hQ : DiscreteConvex (positiveLog w))
    {lam δ : ℝ} (hlam : Real.log 3 < lam) (hδ : lam < δ)
    (hqp : ∀ᶠ n : ℕ in atTop, δ*(n:ℝ)^2 ≤ negativeLog w n)
    (hqq : ∀ᶠ n : ℕ in atTop, δ*(n:ℝ)^2 ≤ positiveLog w n) :
    SupportSeparation w := by sorry
