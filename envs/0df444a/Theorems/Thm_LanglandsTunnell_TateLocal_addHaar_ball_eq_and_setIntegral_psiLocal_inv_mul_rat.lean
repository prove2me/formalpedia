-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_addHaar_ball_eq_and_setIntegral_psiLocal_inv_mul_rat
-- name    : LanglandsTunnell.TateLocal.addHaar_ball_eq_and_setIntegral_psiLocal_inv_mul_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/66420288-73fb-5cda-bc1e-8a0ba085bfbc
-- title:
--   Haar volumes of valuation balls and local Gauss-type integrals over ℚᵥ
-- statement:
--   Let $v$ be a height-one prime of the ring of integers of $\mathbb{Q}$, and equip the completion $\mathbb{Q}_v =$ `v.adicCompletion ℚ` with its Borel $\sigma$-algebra (`localBorel`). The assertion is made for every measure $\nu$ on $\mathbb{Q}_v$ that is an additive Haar measure, and has two parts. First, writing $B_j = \{y \in \mathbb{Q}_v : \mathrm{v}(y) \le \exp(j)\}$ for the valuation ball attached to $j \in \mathbb{Z}$ (the valuation taking values in $\mathbb{Z}_{m0}$, $\exp$ being the embedding of $\mathbb{Z}$ into its group of units): for every $j \in \mathbb{Z}$ one has $0 < \nu(B_j)$, $\nu(B_j) < \infty$, and the real number $\nu(B_j)$ equals $(\mathrm{absNorm}\, v)^{j}\,\nu(B_0)$, where $\mathrm{absNorm}\, v$ is the absolute norm of the ideal $v$ and $B_0 = \{y : \mathrm{v}(y) \le 1\}$. Second, let $\psi =$ `psiLocal ℚ v` be the additive character of $\mathbb{Q}_v$ obtained by composing the standard adelic additive character `stdAddChar` of the adele ring of $\mathbb{Q}$ with the additive map sending $x \in \mathbb{Q}_v$ to the finite adele supported at $v$ with component $x$. Then for all $t \in \mathbb{Q}_v$ and all $j \in \mathbb{Z}$, $$\int_{B_j} \psi^{-1}(t y)\, d\nu(y) = \begin{cases} \nu(B_j) & \text{if } \mathrm{v}(t) \le \exp(-j),\\ 0 & \text{otherwise},\end{cases}$$ the value $\nu(B_j)$ being read as a complex number via its real value.
--
--   This is the one-dimensional local input of Tate-type harmonic analysis at a finite place of $\mathbb{Q}$: the scaling of Haar measure on valuation balls together with the orthogonality relation for the standard additive character, whose level at $v$ is $0$. It is used in the Rankin–Selberg and cubic-induction parts of the development, in the Casselman–Shalika style evaluation of spherical local integrals on $\mathrm{GL}_2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_addHaar_ball_eq_and_setIntegral_psiLocal_inv_mul_rat.lean

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_HaarQuotient
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

open UnramifiedWhittaker

theorem LanglandsTunnell.TateLocal.addHaar_ball_eq_and_setIntegral_psiLocal_inv_mul_rat
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    letI := localBorel ℚ v
    ∀ (ν : Measure (v.adicCompletion ℚ)) [ν.IsAddHaarMeasure],
      (∀ j : ℤ, 0 < ν {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp j} ∧
        ν {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp j} < ⊤ ∧
        (ν {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp j}).toReal =
          (Ideal.absNorm v.asIdeal : ℝ) ^ j * (ν {y : v.adicCompletion ℚ | Valued.v y ≤ 1}).toReal) ∧
      (∀ (t : v.adicCompletion ℚ) (j : ℤ),
        ∫ y in {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp j},
            (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ (t * y) ∂ν =
          if Valued.v t ≤ WithZero.exp (-j)
            then ((ν {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp j}).toReal : ℂ) else 0) := by sorry
