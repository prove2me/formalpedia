-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_integrable_apply_antidiagonal_mul_unipotentGL2_mul_addChar_of_mem_principalSeries2
-- name    : LanglandsTunnell.CubicInduction.integrable_apply_antidiagonal_mul_unipotentGL2_mul_addChar_of_mem_principalSeries2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/83d976a9-7fdf-56d8-b343-12f703e62abd
-- title:
--   Integrability of Jacquet's integrand in the dominant range
-- statement:
--   Let $p$ be a height-one prime of the ring of integers of $\mathbb{Q}$ and let $F = \mathbb{Q}_p$ denote the associated adic completion. Let $\chi_0,\chi_1 \colon F^\times \to \mathbb{C}^\times$ be multiplicative homomorphisms (given as a family $\chi$ indexed by `Fin 2`), and suppose there are natural numbers $c_0,c_1$ such that each $\chi_i$ is trivial on `higherUnitsAt ℚ p (cχ i)`, the set of units $u$ of $F$ with $v(u)=1$ and, unless $c_i = 0$, with $v(u-1) \le \exp(-c_i)$. Let $\varpi \in F^\times$ satisfy $v(\varpi) = \exp(-1)$, and assume the dominance condition $\|\chi_0(\varpi)\| < \|\chi_1(\varpi)\|$. Let $f \colon \mathrm{GL}_2(F) \to \mathbb{C}$ lie in `principalSeries2`, i.e. $f$ is locally constant, satisfies $f\big(\begin{smallmatrix}1&x\\0&1\end{smallmatrix} g\big) = f(g)$ for all $x \in F$, and $f(\mathrm{diag}(a_0,a_1)\,g) = \chi_0(a_0)\chi_1(a_1)\,(\|a_0\|/\|a_1\|)^{1/2} f(g)$ for all units $a_0,a_1$. Let $w_0 \in \mathrm{GL}_2(F)$ have matrix $\begin{smallmatrix}0&1\\1&0\end{smallmatrix}$, let $\theta$ be a continuous additive character of $F$ with values in $\mathbb{C}$, and let $g \in \mathrm{GL}_2(F)$. Then, $F$ being given its Borel measurable structure, for every additive Haar measure $\nu$ on $F$ the function $y \mapsto f\big(w_0 \begin{smallmatrix}1&y\\0&1\end{smallmatrix} g\big)\,\theta(y)$ is $\nu$-integrable.
--
--   This is the absolute convergence of the Jacquet–Whittaker integral $W_f(g) = \int_F f(w_0 n(y) g)\,\theta(y)\,d\nu(y)$ for a section $f$ of the normalised principal series of $\mathrm{GL}_2(\mathbb{Q}_p)$, in the range where $\|\chi_0(\varpi)\| < \|\chi_1(\varpi)\|$. It underlies the construction of the Whittaker functional on the principal series, and is used for the bounds on the absolute Jacquet integral, for the explicit evaluation of the integral on flat sections, and for the spherical computation in the unramified case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_integrable_apply_antidiagonal_mul_unipotentGL2_mul_addChar_of_mem_principalSeries2.lean

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction
  AutomorphicForm

theorem LanglandsTunnell.CubicInduction.integrable_apply_antidiagonal_mul_unipotentGL2_mul_addChar_of_mem_principalSeries2
    (p : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (cχ : Fin 2 → ℕ)
    (hcχ : ∀ i, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p (cχ i), χ i u = 1)
    (ϖ : (p.adicCompletion ℚ)ˣ) (hϖ : Valued.v (ϖ : p.adicCompletion ℚ) = WithZero.exp (-1 : ℤ))
    (hdom : ‖((χ 0 ϖ : ℂˣ) : ℂ)‖ < ‖((χ 1 ϖ : ℂˣ) : ℂ)‖)
    (f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hf : f ∈ principalSeries2 p χ)
    (w₀ : GL (Fin 2) (p.adicCompletion ℚ))
    (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])
    (θ : AddChar (p.adicCompletion ℚ) ℂ) (hθ : Continuous θ)
    (g : GL (Fin 2) (p.adicCompletion ℚ)) :
    letI := localBorel ℚ p
    ∀ (ν : Measure (p.adicCompletion ℚ)) [ν.IsAddHaarMeasure],
      Integrable (fun y : p.adicCompletion ℚ => f (w₀ * unipotentGL2 y * g) * θ y) ν := by sorry
