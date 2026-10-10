-- Prove2me | Theorems.Thm_FullyCoupledSDE_Poisson_lemma_3_2_ii_increment
-- name    : FullyCoupledSDE.Poisson.lemma_3_2_ii_increment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:26:10.454418+00:00
-- url     : https://prove2.me/theorems/b1abbcca-e144-4b60-bf57-b52019021099
-- title:
--   Lemma 3.2(ii), p. 1215, η ∈ (0,1) — h̄(y1) − h̄(y2) = ∫([h(·,y1) − h(·,y2)] − [L0(y1) − L0(y2)]u(·,y2)) dμ^{y1}, and h̄ ∈ C^η_b
-- statement:
--   Let $a,b$ satisfy (Aσ) and (Ab) and lie in $C^{\delta,\eta}_b$ with $0<\delta\le1$ and $0<\eta<1$, and let $(\mu^y)_y$ be the invariant family of $\mathscr L_0$. Let $h\in C^{\delta,\eta}_p$, $\bar h(y)=\int h(x,y)\,\mu^y(dx)$, and let $u\in C^{2+\delta,0}_p$ solve $\mathscr L_0(x,y)u(x,y)=h(x,y)-\bar h(y)$ for all $x,y$. Then for all $y_1,y_2\in\mathbb R^{d_2}$ the integrand below is $\mu^{y_1}$-integrable and
--   $$\bar h(y_1)-\bar h(y_2)=\int_{\mathbb R^{d_1}}\Big([h(x,y_1)-h(x,y_2)]-[\mathscr L_0(x,y_1)-\mathscr L_0(x,y_2)]u(x,y_2)\Big)\,\mu^{y_1}(dx).$$
--   In particular $\bar h\in C^\eta_b(\mathbb R^{d_2})$.
--
--   This is formula (3.10) for $\eta\in(0,1)$: the increment of the average in $y$ is controlled by the $x$-regularity of the Poisson solution only, which gives the Hölder regularity of averaged coefficients.
--
--   **Formalization Note** For $\eta\in(0,1)$ one has $[\eta]=0$, so both sums in (3.10) are empty and $\partial^0_y$ is the identity; $u\in C^{2+\delta,(\eta-1)\vee0}_p=C^{2+\delta,0}_p$. $[\mathscr L_0(x,y_1)-\mathscr L_0(x,y_2)]u(x,y_2)$ is the difference of the two frozen operators applied to $u(\cdot,y_2)$.
-- source:
--   Röckner & Xie, Diffusion approximation for fully coupled SDEs, Ann. Probab. 49 (2021), p. 1215, Lemma 3.2(ii), (3.10) with η ∈ (0,1)

import Mathlib
import Definitions.Def_FullyCoupledSDE_Poisson_Setting

namespace FullyCoupledSDE.Poisson

open MeasureTheory

/-- Lemma 3.2(ii) (p. 1215) for `η ∈ (0,1)` (so `[η] = 0` and the sums in (3.10) are empty).
Under (Aσ), (Ab), `a, b ∈ C^{δ,η}_b`, let `h ∈ C^{δ,η}_p` and let `u ∈ C^{2+δ,0}_p` solve
`L0(x,y)u(x,y) = h(x,y) − h̄(y)`. Then for all `y1, y2`,
`h̄(y1) − h̄(y2) = ∫ ([h(x,y1) − h(x,y2)] − [L0(x,y1) − L0(x,y2)]u(x,y2)) μ^{y1}(dx)`
(integrand integrable), and `h̄ ∈ C^η_b(ℝ^{d2})`. -/
theorem lemma_3_2_ii_increment {d1 d2 : ℕ} (hd1 : 1 ≤ d1) (hd2 : 1 ≤ d2)
    (a : E d1 → E d2 → Matrix (Fin d1) (Fin d1) ℝ) (b : E d1 → E d2 → E d1)
    (μ : E d2 → Measure (E d1)) (δ η : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hη0 : 0 < η) (hη1 : η < 1)
    (hσ : AssumpSigma a) (hb : AssumpB b) (ha : CbMat δ η a) (hbb : Cb δ η b)
    (hμ : IsInvariantFamily a b μ)
    (h : E d1 → E d2 → ℝ) (hh : Cp δ η h)
    (u : E d1 → E d2 → ℝ) (hu : Cp2 δ 0 u)
    (hsol : ∀ x y, L0 a b y (fun x' => u x' y) x = h x y - avg μ h y) :
    (∀ y1 y2 : E d2,
      Integrable (fun x => (h x y1 - h x y2) -
          (L0 a b y1 (fun x' => u x' y2) x - L0 a b y2 (fun x' => u x' y2) x)) (μ y1) ∧
      avg μ h y1 - avg μ h y2 =
        ∫ x, ((h x y1 - h x y2) -
          (L0 a b y1 (fun x' => u x' y2) x - L0 a b y2 (fun x' => u x' y2) x)) ∂(μ y1)) ∧
    CbY η (avg μ h) := by sorry

end FullyCoupledSDE.Poisson
