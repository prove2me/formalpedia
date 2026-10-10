-- Prove2me | Theorems.Thm_FullyCoupledSDE_Poisson_step4_holder_in_y
-- name    : FullyCoupledSDE.Poisson.step4_holder_in_y
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:27:13.390391+00:00
-- url     : https://prove2.me/theorems/952d21cd-de30-42ae-a05d-aec70649813a
-- title:
--   Proof of Theorem 2.1, Step 4, p. 1221 — for η ∈ (0,1): |u(x,y1) − u(x,y2)| ≤ C(|y1 − y2|^η ∧ 1)(1 + |x|^m)
-- statement:
--   Let $a,b$ satisfy (Aσ) and (Ab) and lie in $C^{\delta,\eta}_b$ with $0<\delta\le1$ and $0<\eta<1$, let $(\mu^y)_y$ be the invariant family of $\mathscr L_0$, and let $f\in C^{\delta,\eta}_p$ be centered. If $u\in C^{2+\delta,0}_p$ is a centered solution of $\mathscr L_0(x,y)u(x,y)=f(x,y)$, then there are $C,m>0$ with
--   $$|u(x,y_1)-u(x,y_2)|\le C(|y_1-y_2|^\eta\wedge1)(1+|x|^m)\qquad\text{for all }x,y_1,y_2.$$
--
--   Thus $u(x,\cdot)\in C^\eta_b$ with norm of polynomial growth in $x$, i.e. (2.3) for $\eta\in(0,1)$.
--
--   **Formalization Note** The page writes the constant as $C_1([f]_{C^{\delta,\eta}_p}+\|a\|_{C^{\delta,\eta}_b}+\|b\|_{C^{\delta,\eta}_b})$; this dependence is not posed (see the goal), and a constant existing for each fixed $(a,b,f)$ is asked for. The statement is for every centered solution in $C^{2+\delta,0}_p$, which is unique by the case $\eta=0$.
-- source:
--   Röckner & Xie, Diffusion approximation for fully coupled SDEs, Ann. Probab. 49 (2021), p. 1221, proof of Theorem 2.1, Step 4 (case η ∈ (0,1)), display after (3.13)

import Mathlib
import Definitions.Def_FullyCoupledSDE_Poisson_Setting

namespace FullyCoupledSDE.Poisson

open MeasureTheory

/-- Proof of Theorem 2.1, Step 4 (p. 1221), conclusion for `η ∈ (0,1)`. Under (Aσ), (Ab),
`a, b ∈ C^{δ,η}_b` and a centered `f ∈ C^{δ,η}_p`, every centered solution `u ∈ C^{2+δ,0}_p` of
(1.1) satisfies `|u(x,y1) − u(x,y2)| ≤ C(|y1 − y2|^η ∧ 1)(1 + |x|^m)`. -/
theorem step4_holder_in_y {d1 d2 : ℕ} (hd1 : 1 ≤ d1) (hd2 : 1 ≤ d2)
    (a : E d1 → E d2 → Matrix (Fin d1) (Fin d1) ℝ) (b : E d1 → E d2 → E d1)
    (μ : E d2 → Measure (E d1)) (δ η : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hη0 : 0 < η) (hη1 : η < 1)
    (hσ : AssumpSigma a) (hb : AssumpB b) (ha : CbMat δ η a) (hbb : Cb δ η b)
    (hμ : IsInvariantFamily a b μ)
    (f : E d1 → E d2 → ℝ) (hf : Cp δ η f) (hfc : Centered μ f)
    (u : E d1 → E d2 → ℝ) (hu : Cp2 δ 0 u)
    (hsol : ∀ x y, L0 a b y (fun x' => u x' y) x = f x y) (huc : Centered μ u) :
    ∃ C : ℝ, 0 < C ∧ ∃ m : ℝ, 0 < m ∧
      ∀ x y1 y2, |u x y1 - u x y2| ≤ C * min (‖y1 - y2‖ ^ η) 1 * (1 + ‖x‖ ^ m) := by sorry

end FullyCoupledSDE.Poisson
