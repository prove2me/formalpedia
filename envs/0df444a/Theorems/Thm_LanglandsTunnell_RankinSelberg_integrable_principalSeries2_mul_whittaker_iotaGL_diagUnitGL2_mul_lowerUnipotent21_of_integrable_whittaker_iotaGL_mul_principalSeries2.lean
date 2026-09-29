-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_integrable_principalSeries2_mul_whittaker_iotaGL_diagUnitGL2_mul_lowerUnipotent21_of_integrable_whittaker_iotaGL_mul_principalSeries2
-- name    : LanglandsTunnell.RankinSelberg.integrable_principalSeries2_mul_whittaker_iotaGL_diagUnitGL2_mul_lowerUnipotent21_of_integrable_whittaker_iotaGL_mul_principalSeries2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/638cbfc1-40b5-5f08-8a0a-921760b93e91
-- title:
--   Integrability of the unfolded Rankin–Selberg integrand in Bruhat coordinates
-- statement:
--   Let $p$ be a place of $\mathbb{Q}$ coming from a height-one prime of $\mathcal{O}_{\mathbb{Q}}$, write $F = \mathbb{Q}_p$ for the corresponding completion, and let $V : \mathrm{GL}_3(F) \to \mathbb{C}$ be an arbitrary function, $\chi = (\chi_0,\chi_1)$ a pair of homomorphisms $F^{\times} \to \mathbb{C}^{\times}$, and $f : \mathrm{GL}_2(F) \to \mathbb{C}$ a member of `principalSeries2`, i.e. $f$ is locally constant, satisfies $f(n(x)g) = f(g)$ for $n(x) = \bigl(\begin{smallmatrix}1&x\\0&1\end{smallmatrix}\bigr)$, and $f(\mathrm{diag}(a_0,a_1)g) = \chi_0(a_0)\chi_1(a_1)\sqrt{\|a_0\|/\|a_1\|}\,f(g)$. Let $w_{0,p} \in \mathrm{GL}_2(F)$ have underlying matrix $\bigl(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\bigr)$ and let $s \in \mathbb{C}$. With $F$ and $\mathrm{GL}_2(F)$ carrying their Borel structures, the assertion is: for every Haar measure $\mu_2$ on $\mathrm{GL}_2(F)$, every Haar measure $\tau$ on $F^{\times}$ and every additive Haar measure $\nu$ on $F$, if $g \mapsto V(\iota(g))\,f(w_{0,p}g)\,\mathrm{modulus}(\det g)^{s-1/2}$ is $\mu_2$-integrable, where $\iota(g) = \mathrm{diag}(g,1)$ is the embedding `iotaGL` of $\mathrm{GL}_2$ into $\mathrm{GL}_3$, then the function of four variables $(y,t,a,x) \in F \times F^{\times} \times F^{\times} \times F$ given by $$f(w_{0,p}n(y))\,\chi_0(t)\,\mathrm{modulus}(t)^{s-1}\cdot V\bigl(\iota(\mathrm{diag}(a,1))\,u(x)\,\iota(\mathrm{diag}(1,t)n(y))\bigr)\,\chi_1(a)\,\mathrm{modulus}(a)^{s-1},$$ with $u(x) = 1 + x e_{21} \in \mathrm{GL}_3(F)$ the lower unipotent matrix `lowerUnipotent21`, is integrable for the product measure $\nu \otimes (\tau \otimes (\tau \otimes \nu))$. Here $\mathrm{modulus}$ is the module of the local field, which on the adic completion agrees with the normalised absolute value $\|\cdot\|$.
--
--   This is the absolute-convergence step in the local unfolding of the $\mathrm{GL}_3 \times \mathrm{GL}_2$ Rankin–Selberg integral: integrability of the integrand on $\mathrm{GL}_2(F)$ is transferred, through the Bruhat-type parametrisation $g = u(x)\,\mathrm{diag}(a,t)\,n(y)$ of $\mathrm{GL}_2(F)$ up to a positive measure constant, to the four coordinates in which the integral is computed as an iterated $\mathrm{GL}_3 \times \mathrm{GL}_1$ zeta integral. It is used in the evaluation of the local Rankin–Selberg integral against principal-series vectors and in the construction of the primal and dual middle data for the cubic induction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_integrable_principalSeries2_mul_whittaker_iotaGL_diagUnitGL2_mul_lowerUnipotent21_of_integrable_whittaker_iotaGL_mul_principalSeries2.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_LocalOrbitalBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.TateLocal
  LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.RankinSelberg.integrable_principalSeries2_mul_whittaker_iotaGL_diagUnitGL2_mul_lowerUnipotent21_of_integrable_whittaker_iotaGL_mul_principalSeries2
    (p : HeightOneSpectrum (𝓞 ℚ))
    (V : LocalGL3 p → ℂ)
    (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hf : f ∈ principalSeries2 p χ)
    (w₀p : GL (Fin 2) (p.adicCompletion ℚ)) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])
    (s : ℂ) :
    letI := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (τ : Measure (p.adicCompletion ℚ)ˣ) [τ.IsHaarMeasure]
      (ν : Measure (p.adicCompletion ℚ)) [ν.IsAddHaarMeasure],
      Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          (V (iotaGL g) * f (w₀p * g)) *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^
              (s - 1 / 2)) μ₂ →
      Integrable (fun q : p.adicCompletion ℚ × (p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ =>
          f (w₀p * unipotentGL2 q.1) *
            (((χ 0 q.2.1 : ℂˣ) : ℂ) * ((modulus (q.2.1 : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) *
            (V (iotaGL (diagUnitGL2 q.2.2.1) * lowerUnipotent21 q.2.2.2 *
                  iotaGL (diagUnits2 1 q.2.1 * unipotentGL2 q.1)) *
              ((χ 1 q.2.2.1 : ℂˣ) : ℂ) * ((modulus (q.2.2.1 : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)))
        (ν.prod (τ.prod (τ.prod ν))) := by sorry
