-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_measure_unipotentEntry_preimage_mul_eq
-- name    : LanglandsTunnell.CubicInduction.measure_unipotentEntry_preimage_mul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/b0d11193-08e3-5ee6-97ce-68c8ee0872d2
-- title:
--   Haar scaling on the unipotent subgroup: dilating the integral ball
-- statement:
--   Let $v$ be a finite place of $\mathbb{Q}$, i.e. a point of the height-one spectrum of $\mathcal{O}_{\mathbb{Q}}$, write $\mathbb{Q}_v$ for the $v$-adic completion, and equip $\mathrm{GL}_2(\mathbb{Q}_v)$ with its Borel $\sigma$-algebra, as `localGLBorel` does. Let $N$ be the range of the monoid homomorphism `unipotentGL2Hom` on $\mathbb{Q}_v$, that is the subgroup of matrices $\begin{pmatrix}1&x\\0&1\end{pmatrix}$, $x \in \mathbb{Q}_v$ (the homomorphism sends the multiplicative copy of $x$ to this matrix, with inverse obtained by negating $x$). The assertion is that for every Haar measure $\mu_N$ on $N$ and every unit $u \in \mathbb{Q}_v^{\times}$, the $\mu_N$-measure of the set of $y \in N$ whose upper-right entry $y_{01}$ satisfies $\mathrm{Valued.v}(u^{-1} y_{01}) \le 1$ equals $\mathrm{modulus}(u)$, coerced from $\mathbb{R}_{\ge 0}$ to $[0,\infty]$, times the $\mu_N$-measure of the set of $y \in N$ with $\mathrm{Valued.v}(y_{01}) \le 1$. Here $\mathrm{modulus}(a)$ is $0$ for $a = 0$ and otherwise the value of the distributive Haar character of $\mathbb{Q}_v$ at the unit $a$, so $\mathrm{modulus}(u) = |u|_v$ is the normalised absolute value.
--
--   This is the scaling law for Haar measure on $N \cong \mathbb{Q}_v$ under dilation by a unit: the dilate $u\,\mathcal{O}_v$ of the integral ball has measure $|u|_v$ times that of $\mathcal{O}_v$. It is used in the local integrability estimates for Rankin–Selberg and Whittaker integrands, where the constant term along the unipotent radical is integrated against a gauge.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_measure_unipotentEntry_preimage_mul_eq.lean

import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm

theorem LanglandsTunnell.CubicInduction.measure_unipotentEntry_preimage_mul_eq (v : HeightOneSpectrum (𝓞 ℚ)) :
    letI := localGLBorel ℚ v
    ∀ (μN : Measure ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μN.IsHaarMeasure] (u : (v.adicCompletion ℚ)ˣ),
      μN ((fun y : ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range =>
            ((y : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 1) ⁻¹'
          ((fun z => ((u⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * z) ⁻¹'
            {z : v.adicCompletion ℚ | Valued.v z ≤ 1})) =
        (LanglandsTunnell.TateLocal.modulus ((u : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ENNReal) *
          μN ((fun y : ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range =>
            ((y : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 1) ⁻¹'
            {z : v.adicCompletion ℚ | Valued.v z ≤ 1}) := by sorry
