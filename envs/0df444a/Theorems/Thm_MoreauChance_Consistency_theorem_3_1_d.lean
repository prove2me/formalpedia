-- Prove2me | Theorems.Thm_MoreauChance_Consistency_theorem_3_1_d
-- name    : MoreauChance.Consistency.theorem_3_1_d
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:23:45.669804+00:00
-- url     : https://prove2.me/theorems/4711cfa2-9f92-4794-834f-ecd6227ee77d
-- title:
--   Theorem 3.1 d), p. 9 — ϕ and ϕλ are sequentially weakly upper semicontinuous
-- statement:
--   In the setting of Theorem 3.1 (separable Hilbert $\mathcal H$, Banach $\mathcal Y$, $\xi$ with a Lebesgue density, conic setting (9)–(10) with $\mathcal K$ closed, $\Phi$ continuous), assume the function $h$ of (10) is sequentially weakly continuous. Then $\varphi$ and, for every $\lambda>0$, $\varphi_\lambda$ are sequentially weakly upper semicontinuous: for every weakly convergent sequence $x_k\rightharpoonup x$,
--   $$
--   \limsup_{k\to\infty}\varphi(x_k)\le\varphi(x),\qquad \limsup_{k\to\infty}\varphi_\lambda(x_k)\le\varphi_\lambda(x).
--   $$
--
--   Weak upper semicontinuity makes the feasible set $M(p)$ weakly closed, which together with coercivity of the objective gives existence of optimal solutions of (P).
--
--   **Formalization Note** The page states d) without the weak continuity of $h$, but its proof (p. 11) uses "the sequentially weak continuity of h"; the formalization adds it as a hypothesis. Without it $\varphi$ need not be weakly upper semicontinuous in infinite dimension (take $\mathcal Y=\mathbb R$, $\mathcal K=[0,\infty)$, $\Phi(x,z)=1-\|x\|^2$, $h=\|x\|^2$: then $\varphi=\mathbf 1_{\{\|x\|\ge1\}}$, and an orthonormal sequence converges weakly to $0$). When $\mathcal H$ is finite-dimensional the hypothesis is automatic, since $h$ is continuous.
-- source:
--   van Ackooij, Pérez-Aros, Soto & Vilches, Inner Moreau envelope of nonsmooth conic chance constrained optimization problems, arXiv:2301.09803v1, p. 9, Theorem 3.1 d); proof p. 11

import Mathlib
import Definitions.Def_MoreauChance_Consistency_Basic
import Definitions.Def_MoreauChance_Consistency_Setting

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace MoreauChance.Consistency

theorem theorem_3_1_d
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m : ℕ} (ξ : Ω → EuclideanSpace ℝ (Fin m)) (hξ : Measurable ξ)
    (hdens : Measure.map ξ μ ≪ volume)
    (K : Set Y) (C : Set (StrongDual ℝ Y)) (h : H → ℝ) (Φ : H → EuclideanSpace ℝ (Fin m) → Y)
    (hset : IsConicSetting K C h Φ)
    (hΦ : Continuous (fun q : H × EuclideanSpace ℝ (Fin m) => Φ q.1 q.2))
    (h_weak : SeqWeakCont h) :
    (∀ (xk : ℕ → H) (x : H), WeakConv xk x →
        limsup (fun k => probFun K Φ μ ξ (xk k)) atTop ≤ probFun K Φ μ ξ x) ∧
      (∀ l : ℝ, 0 < l → ∀ (xk : ℕ → H) (x : H), WeakConv xk x →
        limsup (fun k => probFunReg C h Φ μ ξ l (xk k)) atTop ≤ probFunReg C h Φ μ ξ l x) := by sorry

end MoreauChance.Consistency
