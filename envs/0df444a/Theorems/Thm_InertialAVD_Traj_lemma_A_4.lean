-- Prove2me | Theorems.Thm_InertialAVD_Traj_lemma_A_4
-- name    : InertialAVD.Traj.lemma_A_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:06:56.978418+00:00
-- url     : https://prove2.me/theorems/0ede40a6-5f33-4e6c-bb96-be2aa98e3e97
-- title:
--   Lemma A.4 — if $t\ddot w+\alpha\dot w\le g$ with $\alpha>1$, $g\ge0$ integrable and $w$ bounded below, then $[\dot w]_+\in L^1$ and $\lim w(t)$ exists
-- statement:
--   Let $\delta>0$ and $\alpha>1$. Let $w:[\delta,+\infty[\to\mathbb R$ be bounded from below and twice differentiable on $[\delta,+\infty[$ (one-sided at $\delta$), with first derivative $\dot w$ and second derivative $\ddot w$. Let $g$ be a nonnegative function in $L^1(\delta,+\infty)$, and assume
--   $$t\,\ddot w(t)+\alpha\,\dot w(t)\le g(t)\quad\text{for almost every }t>\delta. \tag{81}$$
--   Then the positive part $[\dot w]_+=\max(\dot w,0)$ belongs to $L^1(\delta,+\infty)$, and $\lim_{t\to+\infty}w(t)$ exists in $\mathbb R$.
--
--   This lemma turns the differential inequality (7) for $h_{x^*}$ into the convergence of $\|x(t)-x^*\|$, the first hypothesis of Opial's lemma in the proof of Theorem 2.16.
--
--   **Formalization Note** The page writes $L^1(t_0,+\infty)$ in the conclusion, a slip for $L^1(\delta,+\infty)$; the corrected interval is used. The page assumes $w$ continuously differentiable and uses $\ddot w$ in (81); here $\dot w$ is assumed differentiable at every $t\ge\delta$ (which makes $w$ continuously differentiable). This everywhere hypothesis is stronger than an almost-everywhere one, and it holds in the application $w=h_{x^*}$ along a solution of (1). Nonnegativity of $g$ and (81) are required almost everywhere on $]\delta,+\infty[$.
-- source:
--   Attouch, Chbani, Peypouquet, Redont, Fast convergence of inertial dynamics and algorithms with asymptotic vanishing damping, Optimization Online preprint 5179 (Oct. 2015), p. 24, Lemma A.4, (81)

import Mathlib

open Filter Topology MeasureTheory

namespace InertialAVD.Traj

theorem lemma_A_4 (δ : ℝ) (hδ : 0 < δ) (α : ℝ) (hα : 1 < α) (w w' w'' g : ℝ → ℝ)
    (hw : ∀ t ∈ Set.Ici δ, HasDerivWithinAt w (w' t) (Set.Ici δ) t)
    (hw' : ∀ t ∈ Set.Ici δ, HasDerivWithinAt w' (w'' t) (Set.Ici δ) t)
    (hbdd : BddBelow (w '' Set.Ici δ))
    (hineq : ∀ᵐ t ∂(volume.restrict (Set.Ioi δ)), t * w'' t + α * w' t ≤ g t)
    (hg_nonneg : ∀ᵐ t ∂(volume.restrict (Set.Ioi δ)), 0 ≤ g t)
    (hg_int : IntegrableOn g (Set.Ioi δ)) :
    IntegrableOn (fun t => max (w' t) 0) (Set.Ioi δ) ∧ ∃ ℓ : ℝ, Tendsto w atTop (𝓝 ℓ) := by sorry

end InertialAVD.Traj
