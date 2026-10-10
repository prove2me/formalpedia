-- Prove2me | Theorems.Thm_FullyCoupledSDE_Poisson_step3_rhs_centered
-- name    : FullyCoupledSDE.Poisson.step3_rhs_centered
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:26:49.594986+00:00
-- url     : https://prove2.me/theorems/f8412f39-a9b6-4ffe-99d5-ab8ebd9ef4ea
-- title:
--   Proof of Theorem 2.1, Step 3, p. 1220 — the right-hand side ∂_y f − ∂_yL0 · u of (3.12) satisfies the centering condition
-- statement:
--   Let $a,b$ satisfy (Aσ) and (Ab) and lie in $C^{\delta,1}_b$ with $0<\delta\le1$, let $(\mu^y)_y$ be the invariant family of $\mathscr L_0$, and let $f\in C^{\delta,1}_p$ be centered. Let $u\in C^{2+\delta,0}_p$ solve $\mathscr L_0(x,y)u(x,y)=f(x,y)$. Then for every $y$ and direction $v\in\mathbb R^{d_2}$ the right-hand side of the differentiated equation (3.12) is $\mu^y$-integrable and centered:
--   $$\int_{\mathbb R^{d_1}}\Big[\partial_yf(x,y)\cdot v-\Big(\frac{\partial\mathscr L_0}{\partial y}(x,y)\cdot v\Big)u(x,y)\Big]\,\mu^y(dx)=0.$$
--
--   This is what makes the differentiated equation $\mathscr L_0\,\partial_yu=\partial_yf-\frac{\partial\mathscr L_0}{\partial y}u$ solvable in the centered class, the first step of the induction on $\eta$.
--
--   **Formalization Note** The page obtains the display from (3.9) with $h=f$, $\bar f=0$; only $u\in C^{2+\delta,0}_p$ is needed, so the statement does not assume $u$ centered or more regular in $y$. Directional derivative in $y$ as in Remark 3.3(ii).
-- source:
--   Röckner & Xie, Diffusion approximation for fully coupled SDEs, Ann. Probab. 49 (2021), p. 1220, proof of Theorem 2.1, Step 3, display after (3.12)

import Mathlib
import Definitions.Def_FullyCoupledSDE_Poisson_Setting

namespace FullyCoupledSDE.Poisson

open MeasureTheory

/-- Proof of Theorem 2.1, Step 3 (p. 1220), the display after (3.12). Under (Aσ), (Ab),
`a, b ∈ C^{δ,1}_b`, for a centered `f ∈ C^{δ,1}_p` and any `u ∈ C^{2+δ,0}_p` solving (1.1), the
right-hand side of (3.12) is centered: for every `y` and direction `v`,
`∫ [∂_y f(x,y)·v − (∂L0/∂y)(x,y)·v u(x,y)] μ^y(dx) = 0`, the integrand being integrable. -/
theorem step3_rhs_centered {d1 d2 : ℕ} (hd1 : 1 ≤ d1) (hd2 : 1 ≤ d2)
    (a : E d1 → E d2 → Matrix (Fin d1) (Fin d1) ℝ) (b : E d1 → E d2 → E d1)
    (μ : E d2 → Measure (E d1)) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hσ : AssumpSigma a) (hb : AssumpB b) (ha : CbMat δ 1 a) (hbb : Cb δ 1 b)
    (hμ : IsInvariantFamily a b μ)
    (f : E d1 → E d2 → ℝ) (hf : Cp δ 1 f) (hfc : Centered μ f)
    (u : E d1 → E d2 → ℝ) (hu : Cp2 δ 0 u)
    (hsol : ∀ x y, L0 a b y (fun x' => u x' y) x = f x y) :
    ∀ y v : E d2,
      Integrable (fun x => fderiv ℝ (f x) y v - dL0 a b y v (fun x' => u x' y) x) (μ y) ∧
      ∫ x, (fderiv ℝ (f x) y v - dL0 a b y v (fun x' => u x' y) x) ∂(μ y) = 0 := by sorry

end FullyCoupledSDE.Poisson
