-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_integral_transposeInvN_mul_integral_integral_diagUnits2_eq_integral_upperUnipotent2_mul_of_mem_principalSeries2
-- name    : LanglandsTunnell.CubicInduction.integral_transposeInvN_mul_integral_integral_diagUnits2_eq_integral_upperUnipotent2_mul_of_mem_principalSeries2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/2dc51487-1171-5c81-bbe3-b518afe6478e
-- title:
--   Unfolded dual and primal (3,2) local integrals agree
-- statement:
--   Let $p$ be a height-one prime of the ring of integers of $\mathbb{Q}$ and write $F = \mathbb{Q}_p$ for the completion `p.adicCompletion ℚ`, equipped with its Borel $\sigma$-algebra `localBorel`. Let $\psi$ be an additive character of $F$ with values in $\mathbb{C}$ and let $W \colon \mathrm{GL}_3(F) \to \mathbb{C}$ be a $\psi$-Whittaker function, i.e. $W(n(x,y,z)g) = \psi(x+y)W(g)$ for all $x,y,z \in F$ and $g$, where $n(x,y,z)$ is the upper unipotent matrix with entries $x,y,z$ in positions $(1,2),(2,3),(1,3)$; let $\omega \colon F^\times \to \mathbb{C}^\times$ be a homomorphism with $W(zg) = \omega(z)W(g)$ for scalar matrices $z$. Let $\chi = (\chi_0,\chi_1)$ be a pair of characters of $F^\times$ and let $f$ lie in `principalSeries2`, i.e. $f \colon \mathrm{GL}_2(F) \to \mathbb{C}$ is locally constant, invariant under left translation by the upper unipotent matrices $n(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$, and satisfies $f(\mathrm{diag}(a_0,a_1)g) = \mathrm{torusChar2}(\chi)(a)\,\sqrt{\lVert a_0\rVert/\lVert a_1\rVert}\,f(g)$. Let $w_0 \in \mathrm{GL}_2(F)$ have matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ and let $s \in \mathbb{C}$. Then for every left-invariant measure $\mu$ on $F^\times$ and every additive Haar measure $\nu$ on $F$,
--   $$\int_F f\bigl(w_0\,{}^{t}(w_0 n(y))^{-1}\bigr)\,\mathcal{W}\bigl(w_3\,n(0,0,-y)\,w_3\,w'\bigr)\,d\nu(y) = \int_F f\bigl(w_0 n(y)\bigr)\,\mathcal{W}\bigl(w_3\,n(0,0,y)\,w'\bigr)\,d\nu(y),$$
--   where $\mathcal{W}(k) = \int_{F^\times}\int_{F^\times} \chi_1(a)^{-1}\omega(a)^{-1}\lvert a\rvert^{s}\,\chi_0(t)\lvert t\rvert^{-s-1}\,W\bigl(\iota(\mathrm{diag}(ta,a))\,k\bigr)\,d\mu(t)\,d\mu(a)$, with $\lvert\cdot\rvert$ the module `modulus` of $F$, $\iota$ the embedding $M \mapsto \mathrm{diag}(M,1)$ of $\mathrm{GL}_2$ into $\mathrm{GL}_3$, $w_3$ the antidiagonal permutation matrix in $\mathrm{GL}_3(F)$ and $w'$ the permutation matrix interchanging the last two coordinates.
--
--   This is the final identification in the proof that the local gamma factor for $\mathrm{GL}_3 \times \mathrm{GL}_2$ is multiplicative in the $\mathrm{GL}_2$ variable when the $\mathrm{GL}_2$ datum is a principal series: after the two $\mathrm{GL}_3 \times \mathrm{GL}_1$ functional equations have been applied, the unfolded dual integral over the big Bruhat cell coincides term by term with the unfolded primal one. It feeds the Rankin–Selberg statement comparing local integrals with Jacquet integrals of principal-series sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_integral_transposeInvN_mul_integral_integral_diagUnits2_eq_integral_upperUnipotent2_mul_of_mem_principalSeries2.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_SmoothingKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.integral_transposeInvN_mul_integral_integral_diagUnits2_eq_integral_upperUnipotent2_mul_of_mem_principalSeries2
    (p : HeightOneSpectrum (𝓞 ℚ))

    (ψ : AddChar (p.adicCompletion ℚ) ℂ) (W : LocalGL3 p → ℂ) (hW : IsGL3PsiWhittakerFn ψ W)
    (ω : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (hω : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : LocalGL3 p),
      W (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) = ((ω z : ℂˣ) : ℂ) * W g)

    (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (f : LocalGL2 p → ℂ) (hf : f ∈ principalSeries2 p χ)
    (w₀p : LocalGL2 p) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])
    (s : ℂ) :
    letI := localBorel ℚ p
    ∀ (μ : Measure (p.adicCompletion ℚ)ˣ) [μ.IsMulLeftInvariant]
      (ν : Measure (p.adicCompletion ℚ)) [ν.IsAddHaarMeasure],
      (∫ y : p.adicCompletion ℚ,
          f (w₀p * AutomorphicForm.transposeInvN (Fin 2) (w₀p * upperUnipotent2 p y)) *
            (∫ a : (p.adicCompletion ℚ)ˣ, ∫ t : (p.adicCompletion ℚ)ˣ,
              ((((χ 1) a : ℂˣ) : ℂ)⁻¹ * ((ω a : ℂˣ) : ℂ)⁻¹ * ((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s *
                ((((χ 0) t : ℂˣ) : ℂ) * ((modulus (t : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-s - 1))) *
              W (iotaGL (diagUnits2 (t * a) a) *
                (longWeyl3 * upperUnipotent3 0 0 (-y) * longWeyl3 * weylPrime3)) ∂μ ∂μ) ∂ν) =
        ∫ y : p.adicCompletion ℚ,
          f (w₀p * upperUnipotent2 p y) *
            (∫ a : (p.adicCompletion ℚ)ˣ, ∫ t : (p.adicCompletion ℚ)ˣ,
              ((((χ 1) a : ℂˣ) : ℂ)⁻¹ * ((ω a : ℂˣ) : ℂ)⁻¹ * ((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s *
                ((((χ 0) t : ℂˣ) : ℂ) * ((modulus (t : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-s - 1))) *
              W (iotaGL (diagUnits2 (t * a) a) *
                (longWeyl3 * upperUnipotent3 0 0 y * weylPrime3)) ∂μ ∂μ) ∂ν := by sorry
