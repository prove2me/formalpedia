-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_exists_const_rsArchIntegral_eq_mul_integral_diagonal
-- name    : LanglandsTunnell.Converse.exists_const_rsArchIntegral_eq_mul_integral_diagonal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/75dcfdfb-0345-5083-bd57-333d1c35428e
-- title:
--   Iwasawa reduction of the archimedean Rankin–Selberg integral
-- statement:
--   Give $\mathrm{GL}_2(\mathbb{R})$ its Borel $\sigma$-algebra, and assume that [`RSCarrier.archMeasure`](def/LanglandsTunnell_RSCarrierSplit.html#L11) — the pullback of Lebesgue measure on $2\times 2$ real matrices along the inclusion of $\mathrm{GL}_2(\mathbb{R})$, weighted by $|\det|^{-2}$ — is a Haar measure. Then there is a constant $c>0$, depending on nothing further, such that the following holds for every Haar measure $\mu_N$ on `realUnipotent`, the image of $\mathbb{R}$ under $x\mapsto \begin{pmatrix}1&x\\0&1\end{pmatrix}$, every $s\in\mathbb{C}$ and all functions $W,F\colon \mathrm{GL}_2(\mathbb{R})\to\mathbb{C}$ subject to: $W(ng)F(ng)=W(g)F(g)$ for all $n$ in `realUnipotent` and all $g$; $W(gk)F(gk)=W(g)F(g)$ for all $g$ and all $k$ in `rowIsometrySubgroup ℝ` (those $k$ with $|\det k|=1$ for which $(x,y)\mapsto (x,y)k$ preserves $\|x\|^2+\|y\|^2$) with $\det k=1$; $W$ and $F$ measurable; and $g\mapsto W(g)F(g)\,|\det g|^{s-1/2}$ integrable against `archMeasure` weighted by the density [`HaarQuotient.density realUnipotent μN`](def/HaarQuotient.html#L25). Under these hypotheses the archimedean Rankin–Selberg integral $\mathrm{rsArchIntegral}$, namely $\int W(g)F(g)\,|\det g|^{s-1/2}$ against that weighted measure, equals
--   $$\frac{c}{\mu_N(\{n : n_{01}\in[0,1]\})}\int_{0}^{\infty}\int_{\mathbb{R}} W(p)F(p)\,|\det p|^{s-1/2}\,a_1^{-2}\,da_1\,da_2,$$
--   where $p=\begin{pmatrix}a_1&0\\0&a_2\end{pmatrix}$ and the inner integrand is read as $0$ when $a_1=0$ (or $a_2\le 0$).
--
--   This is the Iwasawa-coordinate unfolding of the archimedean Rankin–Selberg integral over $N_2(\mathbb{R})\backslash\mathrm{GL}_2(\mathbb{R})$: the integral is rewritten as an integral over the diagonal torus against $da_1\,da_2/a_1^{2}$, with a positive constant uniform in $\mu_N$, $s$, $W$ and $F$, and the normalising factor $1/\mu_N(\{n_{01}\in[0,1]\})$ making both sides scale identically in $\mu_N$. It is the computational input to the subsequent torus identities and to the evaluations of the archimedean integral for Gaussian test data in terms of $\Gamma$-factors and Mellin transforms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_exists_const_rsArchIntegral_eq_mul_integral_diagonal.lean

import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AutomorphicForm_RowIsometryInvariance

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCoordinates RSCarrier

theorem LanglandsTunnell.Converse.exists_const_rsArchIntegral_eq_mul_integral_diagonal :
    letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
    ∀ (_hHaar : RSCarrier.archMeasure.IsHaarMeasure),
    ∃ c : ℝ, 0 < c ∧
      ∀ (μN : Measure realUnipotent) [μN.IsHaarMeasure] (s : ℂ) (W F : GL (Fin 2) ℝ → ℂ)
        (_hN : ∀ n ∈ realUnipotent, ∀ g : GL (Fin 2) ℝ, W (n * g) * F (n * g) = W g * F g)
        (_hK : ∀ k ∈ rowIsometrySubgroup ℝ, Matrix.GeneralLinearGroup.det k = 1 →
          ∀ g : GL (Fin 2) ℝ, W (g * k) * F (g * k) = W g * F g)
        (_hW : Measurable W) (_hF : Measurable F)
        (_hint : Integrable
          (fun g : GL (Fin 2) ℝ =>
            (W g * F g) * (((|(Matrix.GeneralLinearGroup.det g : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2)))
          (RSCarrier.archMeasure.withDensity (HaarQuotient.density realUnipotent μN))),
        rsArchIntegral RSCarrier.archMeasure μN s W F =
          ((c / (μN {n : realUnipotent |
              ((n : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 ∈ Set.Icc (0 : ℝ) 1}).toReal : ℝ) : ℂ) *
            ∫ a₂ in Set.Ioi (0 : ℝ), ∫ a₁ : ℝ,
              if h : a₁ ≠ 0 ∧ 0 < a₂ then
                let p : GL (Fin 2) ℝ := upperUnit a₁ 0 a₂ h.1 h.2.ne'
                ((W p * F p) * (((|(Matrix.GeneralLinearGroup.det p : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2))) *
                  (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)
              else 0 := by sorry
