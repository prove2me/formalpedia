-- Prove2me | Theorems.Thm_OAI_BackwardIntertwiners_EnvelopeBounds_correlation_budget
-- name    : OAI.BackwardIntertwiners.EnvelopeBounds.correlation_budget
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:18:43.51658+00:00
-- url     : https://prove2.me/theorems/4d5dd28a-00a7-4cef-9539-55d12e665d05
-- title:
--   Correlation budget: a vanishing centred correlation forces a lower bound on geometric and tail sums
-- statement:
--   A function $F:\mathbb{N}\to\mathbb{R}$ is *discretely convex* if its increments $F(n+1)-F(n)$ form a nondecreasing sequence, equivalently if its second differences $\Delta^2F(n)=F(n+2)-2F(n+1)+F(n)$ are all $\ge0$. For $F:\mathbb{N}\to\mathbb{R}$ and $q,k\in\mathbb{N}$, the *normalized tail term* is $T_F(q,k)=\exp\bigl(F(k+1)+F(q)-F(q+k+1)\bigr)$. For $A,B:\mathbb{N}\to\mathbb{R}$ and $b,c:\mathbb{Z}\to\mathbb{C}$, say that $(b,c)$ satisfies the *envelope bounds with profiles* $(A,B)$ if for every $n\in\mathbb{N}$
--   $$|b(n)|\le e^{-B(n)},\qquad|b(-n)|\le e^{A(n)},\qquad|c(n)|\le e^{B(n)},\qquad|c(-n)|\le e^{-A(n)}.$$
--   For $m,p\in\mathbb{N}$ the *centred correlation* is $\gamma_{m,p}(n)=b(p+n)\,c(n-m)$ for $n\in\mathbb{Z}$, and for $\lambda\in\mathbb{R}$ put $g_\lambda(k)=e^{-\lambda(k+1)}$.
--
--   Assume:
--   1. $(b,c)$ satisfies the envelope bounds with profiles $(A,B)$;
--   2. $A$ and $B$ are discretely convex with $A(0)=B(0)=0$;
--   3. $\sum_{n\ge0}e^{-(A(n+1)-A(n))}<\infty$ and $\sum_{n\ge0}e^{-(B(n+1)-B(n))}<\infty$;
--   4. $m\ge1$, $p\ge1$, $\lambda>0$, and the two *bridge inequalities* hold:
--   $$A(m)-A(m-1)+\lambda\le B(p+1)-B(p),\qquad B(p)-B(p-1)+\lambda\le A(m+1)-A(m);$$
--   5. the bounds are attained at the centre: $|b(p)|=e^{-B(p)}$ and $|c(-m)|=e^{-A(m)}$;
--   6. $\sum_{n\in\mathbb{Z}}\gamma_{m,p}(n)=0$.
--
--   Then
--   $$1\le2\sum_{k=0}^{\infty}g_\lambda(k)+\sum_{k=0}^{\infty}T_A(m+p,k)+\sum_{k=0}^{\infty}T_B(m+p,k).$$
--
--   The central term $\gamma_{m,p}(0)=b(p)\,c(-m)$ has modulus $e^{-B(p)-A(m)}$, and the bridge inequalities make all other terms smaller by geometric factors near the centre and by tail factors far from it; the theorem quantifies that the centre cannot be cancelled unless this budget is at least $1$. Since $2\sum_kg_\lambda(k)=2e^{-\lambda}/(1-e^{-\lambda})<1$ for $\lambda>\log3$ and the tail sums become small for large $m+p$, the inequality fails for suitable large indices, which is how the project rules out vanishing correlations.
--
--   **Formalization Note** The envelope bounds are the structure `EnvelopeBounds A B b c`, $\gamma_{m,p}$ is `centeredCorrelation b c m p`, $g_\lambda$ is `geometricMiddle lam` and $T_F$ is `normalizedTailTerm F`. All sums are Mathlib's unconditional sums `tsum`, which are $0$ for non-summable families; under the stated hypotheses all families involved are summable, so the sums are ordinary convergent sums.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BackwardIntertwiners/ConvolutionBounds.lean#L175-L232

import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvolutionBounds

open OAI OAI.BackwardIntertwiners OAI.BackwardIntertwiners.EnvelopeBounds
open Filter
open scoped Topology
variable {A B : ℕ → ℝ} {b c : ℤ → ℂ}

theorem OAI.BackwardIntertwiners.EnvelopeBounds.correlation_budget (hb : EnvelopeBounds A B b c)
    (hA : DiscreteConvex A) (hB : DiscreteConvex B)
    (hA0 : A 0 = 0) (hB0 : B 0 = 0)
    (hsA : Summable (fun n => Real.exp (-(A (n+1) - A n))))
    (hsB : Summable (fun n => Real.exp (-(B (n+1) - B n))))
    {m p : ℕ} (hm : 1 ≤ m) (hp : 1 ≤ p) {lam : ℝ} (hlam : 0 < lam)
    (hbridge₁ : A m - A (m-1) + lam ≤ B (p+1) - B p)
    (hbridge₂ : B p - B (p-1) + lam ≤ A (m+1) - A m)
    (hcB : ‖b (p : ℤ)‖ = Real.exp (-B p))
    (hcA : ‖c (-(m : ℤ))‖ = Real.exp (-A m))
    (hz : (∑' n : ℤ, centeredCorrelation b c m p n) = 0) :
    1 ≤ 2 * (∑' k, geometricMiddle lam k) +
      (∑' k, normalizedTailTerm A (m+p) k) +
      (∑' k, normalizedTailTerm B (m+p) k) := by sorry
