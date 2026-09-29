-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_gauge3_le_mul_archRoot_mul_archRoot_sq_of_siegel_of_ideleNorm_det_mem_Icc
-- name    : LanglandsTunnell.CubicInduction.exists_gauge3_le_mul_archRoot_mul_archRoot_sq_of_siegel_of_ideleNorm_det_mem_Icc
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/8bed1864-8e12-5c36-9c4c-01645be65538
-- title:
--   Uniform gauge bound on a Siegel set determinant slab
-- statement:
--   Let $c, C, a, b$ be reals with $0 < c$, $0 < a$ and $a < b$. The assertion is that there exists $W \in \mathbb{R}$ with $0 \le W$ such that for all $n, t, k \in \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ (i.e. `GL (Fin 3)` over the adele ring of $\mathbb{Q}$) the following holds. Suppose: at every height-one prime $p$ of $\mathcal{O}_{\mathbb{Q}}$ the $p$-component of $n$ is $1$, and likewise for $t$; the $p$-component of $k$ lies in `localMaximalCompact3`, that is, all entries of this component and of its inverse have valuation $\le 1$ in the $p$-adic completion. Suppose further that for every infinite place $w$ of $\mathbb{Q}$, writing matrices over $w$'s completion: the component of $n$ at $w$ has all diagonal entries equal to $1$, all entries strictly below the diagonal equal to $0$, and every entry of norm $\le C$; the component of $t$ at $w$ has all off-diagonal entries $0$; $c \le$ `archRoot₁ ℚ w t` and $c \le$ `archRoot₂ ℚ w t`; and the component of $k$ at $w$ satisfies $k_w^{\mathsf T} k_w = 1$. Suppose finally that `ideleNorm` of $\det(n t k)$ — the value at that idele of the distributive Haar character of the adele ring, viewed as a real number — lies in $[a,b]$. Then for every infinite place $w$ of $\mathbb{Q}$, $$\mathtt{gauge3}\,\mathbb{Q}\,(n t k) \le W \cdot \bigl(\mathtt{archRoot₁}\,\mathbb{Q}\,w\,t \cdot \mathtt{archRoot₂}\,\mathbb{Q}\,w\,t\bigr)^2,$$ where `gauge3` of $g$ is $\max\bigl(1, (1 + \sum_w \mathtt{matrixSize}(g_w)) \cdot \prod_v \mathtt{matrixSupSize}(g_v)\bigr)$, the sum over infinite places and the (finitely supported) product over height-one primes. Since $\mathbb{Q}$ has a single infinite place, the outer quantifier over $w$ in the conclusion amounts to one instance; $W$ depends only on $c, C, a, b$.
--
--   This is the reduction-theory height estimate for $\mathrm{GL}_3$: on a Siegel set, intersected with a slab $\|\det g\|_{\mathbb{A}} \in [a,b]$ for the idelic norm, the adelic gauge (a height function built from the entries of $g$ at all places) is bounded by a constant multiple of the square of the product of the two simple-root coordinates of the torus part. It is used by [`LanglandsTunnell.CubicInduction.norm_mul_gauge3_pow_le_of_siegel_of_isCuspidalAlong_of_archDeriv_growth`](thm.html#LanglandsTunnell.CubicInduction.norm_mul_gauge3_pow_le_of_siegel_of_isCuspidalAlong_of_archDeriv_growth) to convert decay in the simple roots into decay measured against the gauge.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_gauge3_le_mul_archRoot_mul_archRoot_sq_of_siegel_of_ideleNorm_det_mem_Icc.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory
open LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2

theorem LanglandsTunnell.CubicInduction.exists_gauge3_le_mul_archRoot_mul_archRoot_sq_of_siegel_of_ideleNorm_det_mem_Icc
    (c C a b : ℝ) (hc0 : 0 < c) (ha : 0 < a) (hab : a < b) :
    ∃ W : ℝ, 0 ≤ W ∧ ∀ n t k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p n = 1) →
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p t = 1) →
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) →
        (∀ w : InfinitePlace ℚ,
          (∀ i j : Fin 3,
            (archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i i = 1 ∧
            (j < i → (archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
            ‖(archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i j‖ ≤ C) ∧
          (∀ i j : Fin 3, i ≠ j →
            (archPlaceComponent3 ℚ w t : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
          c ≤ archRoot₁ ℚ w t ∧ c ≤ archRoot₂ ℚ w t ∧
          (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion)ᵀ *
              (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion) = 1) →
        NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (n * t * k)) ∈ Set.Icc a b →
        ∀ w : InfinitePlace ℚ, gauge3 ℚ (n * t * k) ≤ W * (archRoot₁ ℚ w t * archRoot₂ ℚ w t) ^ 2 := by sorry
