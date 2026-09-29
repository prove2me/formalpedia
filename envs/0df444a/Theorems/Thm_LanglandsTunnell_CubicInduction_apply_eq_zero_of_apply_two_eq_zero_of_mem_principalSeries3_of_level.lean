-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_apply_eq_zero_of_apply_two_eq_zero_of_mem_principalSeries3_of_level
-- name    : LanglandsTunnell.CubicInduction.apply_eq_zero_of_apply_two_eq_zero_of_mem_principalSeries3_of_level
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/7c30da06-86d6-50d8-86e3-a9b77da10b86
-- title:
--   Vanishing of a level-b principal series vector on the (2,1) parabolic
-- statement:
--   Let $v$ be a nonzero prime of the ring of integers of $\mathbb{Q}$, write $F = \mathbb{Q}_v$ for the $v$-adic completion, let $\chi_0,\chi_1,\chi_2 \colon F^\times \to \mathbb{C}^\times$ be a triple of characters (group homomorphisms on the units of $F$) indexed by `Fin 3`, and let $b$ be a natural number. Assume that each of $\chi_0$ and $\chi_1$ is non-trivial on the set of units $u$ with $\mathrm{v}(u)=1$ subject to the further condition, when $b \neq 0$, that $\mathrm{v}(u-1) \le \exp(-b)$. Let $\Phi \colon GL_3(F) \to \mathbb{C}$ lie in `principalSeries3`, i.e. $\Phi$ is locally constant, $\Phi(n g) = \Phi(g)$ for every upper triangular unipotent $n = \bigl(\begin{smallmatrix} 1 & x & z \\ 0 & 1 & y \\ 0 & 0 & 1\end{smallmatrix}\bigr)$, and $\Phi(\mathrm{diag}(a_0,a_1,a_2)\,g) = \chi_0(a_0)\chi_1(a_1)\chi_2(a_2)\,(\|a_0\|/\|a_2\|)\,\Phi(g)$ for all units $a_i$. Assume moreover that $\Phi$ is invariant under right translation by $\mathrm{diag}(u,1,1)$ for every unit $u$ with $\mathrm{v}(u)=1$, by the upper unipotent with $(0,1)$-entry $s$, and by the lower unipotent with $(1,0)$-entry $s$, for every $s \in F$ with $\mathrm{v}(s) \le \exp(-b)$. Then $\Phi(x) = 0$ for every $x \in GL_3(F)$ whose underlying matrix satisfies $x_{2,0} = x_{2,1} = 0$.
--
--   This is the contribution of the closed Borel–parabolic double coset in the geometric-lemma analysis of the principal series of $GL_3(F)$ along the standard parabolic of type $(2,1)$: on that parabolic a principal series vector is a $GL_2$ principal series vector for $(\chi_0,\chi_1)$, and an Atkin–Lehner type argument forces it to vanish once $\chi_0$ and $\chi_1$ are ramified beyond level $b$. It is cited in the computations of the sums over Weyl elements and of the linear functional attached to the radical of the $(2,1)$ parabolic.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_apply_eq_zero_of_apply_two_eq_zero_of_mem_principalSeries3_of_level.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.apply_eq_zero_of_apply_two_eq_zero_of_mem_principalSeries3_of_level
    (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (b : ℕ)
    (hχ₀ : ∃ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ v b, χ 0 u ≠ 1)
    (hχ₁ : ∃ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ v b, χ 1 u ≠ 1)
    (Φ : LanglandsTunnell.CubicInduction.LocalGL3 v → ℂ)
    (hΦ : Φ ∈ LanglandsTunnell.CubicInduction.principalSeries3 v χ)
    (hdiag : ∀ (g : LanglandsTunnell.CubicInduction.LocalGL3 v) (u : (v.adicCompletion ℚ)ˣ),
      Valued.v (u : v.adicCompletion ℚ) = 1 →
      Φ (g * LanglandsTunnell.CubicInduction.iotaGL (LanglandsTunnell.CubicInduction.diagUnitGL2 u)) = Φ g)
    (hupper : ∀ (g : LanglandsTunnell.CubicInduction.LocalGL3 v) (s : v.adicCompletion ℚ),
      Valued.v s ≤ WithZero.exp (-(b : ℤ)) →
      Φ (g * LanglandsTunnell.CubicInduction.upperUnipotent3 s 0 0) = Φ g)
    (hlower : ∀ (g : LanglandsTunnell.CubicInduction.LocalGL3 v) (s : v.adicCompletion ℚ),
      Valued.v s ≤ WithZero.exp (-(b : ℤ)) →
      Φ (g * LanglandsTunnell.CubicInduction.lowerUnipotent21 s) = Φ g)
    (x : LanglandsTunnell.CubicInduction.LocalGL3 v)
    (h20 : (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0)
    (h21 : (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0) :
    Φ x = 0 := by sorry
