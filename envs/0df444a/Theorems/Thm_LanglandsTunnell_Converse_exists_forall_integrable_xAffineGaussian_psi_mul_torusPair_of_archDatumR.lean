-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_exists_forall_integrable_xAffineGaussian_psi_mul_torusPair_of_archDatumR
-- name    : LanglandsTunnell.Converse.exists_forall_integrable_xAffineGaussian_psi_mul_torusPair_of_archDatumR
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/548df79b-d3a9-5c3a-86a4-8a5fd394fdef
-- title:
--   Integrability of an affine Gaussian–Whittaker torus integrand
-- statement:
--   Fix complex numbers $\nu_1,\nu_2$ and classes $a_1,a_2\in\mathbb Z/2$, and let $W:\mathbb R\to\mathbb C$ be continuous on $\{t\neq 0\}$ and satisfy, for every $b\in\mathbb Z/2$ and every $t>0$, the two-sheet weight-one Gaussian-convolution identity $$W(t)+(-1)^{b}W(-t)=t\cdot 4\int_{0}^{\infty} r^{\nu_1+\mathrm{signShift}(a_1+b)}e^{-\pi r^{2}}\,(t/r)^{\nu_2+\mathrm{signShift}(a_2+b)}e^{-\pi (t/r)^{2}}\,\frac{dr}{r},$$ where $\mathrm{signShift}(a)$ is $0$ for $a=0$ and $1$ otherwise. Let $P_2$ be a real archimedean parameter and $D$ an `ArchDatumR P₂`, that is, a function $D.W$ on real $2\times2$ matrices which is smooth on the invertible locus, satisfies the unipotent law $D.W(u(x)g)=\psi(x)D.W(g)$ and the central law $D.W(zg)=\chi_{P_2}(z)|z|D.W(g)$ for $z\neq0$, whose torus zeta integrals converge in a right half-plane and equal the archimedean factor of the twisted parameter times an entire function of finite order in vertical strips obeying the $\varepsilon$-functional equation, and which satisfies the structure's decay bounds along $\mathrm{diagOne}(y)k$ for $|y|\ge1$ and $0<|y|\le1$. Let $a\neq0$ be real and $c_0,c_1\in\mathbb C$. Then there is $\sigma\in\mathbb R$ such that for every $s$ with $\operatorname{Re}s>\sigma$, every $y_1\neq0$ and every $y_2>0$, the function $$(x,t)\mapsto e^{-\pi x^{2}/y_1^{2}}(c_0+c_1 i x)\,\psi(atx)\cdot W(t)\,D.W\!\left(\mathrm{diagOne}(aty_1/y_2)\right)|t|^{\,s-1/2}\,t^{-2}$$ is integrable on $\mathbb R\times\mathbb R$ for the product of Lebesgue measures, where $\psi(x)=e^{2\pi i x}$ and $\mathrm{diagOne}(y)=\begin{pmatrix}y&0\\0&1\end{pmatrix}$. No hypothesis is imposed on the torus profile of $D$ beyond the fields of the structure itself; the threshold $\sigma$ is uniform in $y_1$ and $y_2$.
--
--   This is the absolute-convergence input for the archimedean computations in the converse-theorem step of the Langlands–Tunnell argument: it licenses Fubini for the Iwasawa-unfolded $(x,t)$-integral attached to a pair of real Whittaker profiles twisted by an affine Gaussian block factor. It is used by the two lemmas identifying the integral of the theta-free Iwasawa integrand (for the harmonic block and for its conjugate) with the corresponding post-Gaussian torus-triple integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_exists_forall_integrable_xAffineGaussian_psi_mul_torusPair_of_archDatumR.lean

import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Mathlib.Analysis.MellinTransform

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField LanglandsTunnell LanglandsTunnell.Converse MeasureTheory

theorem LanglandsTunnell.Converse.exists_forall_integrable_xAffineGaussian_psi_mul_torusPair_of_archDatumR
    (ν₁ ν₂ : ℂ) (a₁ a₂ : ZMod 2)
    (W : ℝ → ℂ) (hWc : ContinuousOn W {t : ℝ | t ≠ 0})
    (hW : ∀ b : ZMod 2, ∀ t : ℝ, 0 < t →
      W t + (-1 : ℂ) ^ b.val * W (-t) =
        (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (a₁ + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂ + signShift (a₂ + b)) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)))
    {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (a : ℝ) (ha : a ≠ 0) (c₀ c₁ : ℂ) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → ∀ y₁ : ℝ, y₁ ≠ 0 → ∀ y₂ : ℝ, 0 < y₂ →
      Integrable (fun q : ℝ × ℝ =>
        ((Real.exp (-(Real.pi * (q.1 ^ 2 / y₁ ^ 2))) : ℂ) * (c₀ + c₁ * Complex.I * (q.1 : ℂ)) * ArchR.psi (a * q.2 * q.1)) *
          (W q.2 * D.W (ArchR.diagOne (a * q.2 * y₁ / y₂)) * (((|q.2| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((q.2 ^ 2)⁻¹ : ℝ) : ℂ)))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by sorry
