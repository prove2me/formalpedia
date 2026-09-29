-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_conj_radical_sub_one_mul_self_eq_zero_and_norm_le_div_archRoot_of_siegel
-- name    : LanglandsTunnell.CubicInduction.conj_radical_sub_one_mul_self_eq_zero_and_norm_le_div_archRoot_of_siegel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/52cfcba2-5c78-5e2e-8702-6bb3489e43b7
-- title:
--   Square-zero conjugate of a radical element past a Siegel point
-- statement:
--   Fix reals $c, C, M'$ with $0 < c$ and three elements $n, t, k$ of $\mathrm{GL}_3$ over the adele ring of $\mathbb{Q}$; for $g$ in that group write $g_\infty$ for its image under `archPlaceComponent3 ℚ Rat.infinitePlace`, i.e. the archimedean component of $g$ evaluated at the real place, viewed as a $3\times 3$ matrix over that completion. Assume: every diagonal entry of $n_\infty$ is $1$, its entries strictly below the diagonal vanish, and every entry has norm at most $C$; all off-diagonal entries of $t_\infty$ vanish; $c \le \mathrm{archRoot}_1(t)$ and $c \le \mathrm{archRoot}_2(t)$ at the real place; and $k_\infty^{\mathsf T} k_\infty = 1$. Let $v : \mathrm{Fin}\ 2 \to \mathbb{A}_{\mathbb{Q}}$ satisfy $\|v(i)_\infty\| \le M'$ for $i = 0,1$, where $v(i)_\infty$ denotes the archimedean component of $v(i)$ at the real place. Put $g = n t k$, $u_{21}(v) = \begin{pmatrix}1&0&v_0\\0&1&v_1\\0&0&1\end{pmatrix}$ and $u_{12}(v) = \begin{pmatrix}1&v_0&v_1\\0&1&0\\0&0&1\end{pmatrix}$. Then, with $X = (g^{-1} u_{21}(v) g)_\infty - 1$, one has $X^2 = 0$ and $\|X_{ij}\| \le 2(1+C)\max(1,c^{-1})M' / \mathrm{archRoot}_2(t)$ for all $i,j$; and the same two conclusions hold for $Y = (g^{-1} u_{12}(v) g)_\infty - 1$ with $\mathrm{archRoot}_1(t)$ in place of $\mathrm{archRoot}_2(t)$.
--
--   This is the Siegel-set estimate showing that conjugating an element of the unipotent radical of either maximal parabolic $P_{2,1}$ or $P_{1,2}$ of $\mathrm{GL}_3$ by a point of a Siegel set produces a square-zero displacement whose entries are damped by the opposite simple root. It is used in the construction of smoothing operators and the verification of cuspidality along these parabolics, via [`LanglandsTunnell.CubicInduction.exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel`](thm.html#LanglandsTunnell.CubicInduction.exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_conj_radical_sub_one_mul_self_eq_zero_and_norm_le_div_archRoot_of_siegel.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.conj_radical_sub_one_mul_self_eq_zero_and_norm_le_div_archRoot_of_siegel
    {c C M' : ℝ} (hc : 0 < c) {n t k : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hnw : ∀ i j : Fin 3,
      (archPlaceComponent3 ℚ Rat.infinitePlace n : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) i i = 1 ∧
      (j < i →
        (archPlaceComponent3 ℚ Rat.infinitePlace n : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) i j = 0) ∧
      ‖(archPlaceComponent3 ℚ Rat.infinitePlace n : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) i j‖ ≤ C)
    (htw : ∀ i j : Fin 3, i ≠ j →
      (archPlaceComponent3 ℚ Rat.infinitePlace t : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) i j = 0)
    (hr₁ : c ≤ archRoot₁ ℚ Rat.infinitePlace t) (hr₂ : c ≤ archRoot₂ ℚ Rat.infinitePlace t)
    (hK : (archPlaceComponent3 ℚ Rat.infinitePlace k :
          Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion)ᵀ *
        (archPlaceComponent3 ℚ Rat.infinitePlace k : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) = 1)
    (v : Fin 2 → AdeleRing (𝓞 ℚ) ℚ)
    (hv : ∀ i : Fin 2, ‖AdelicLevel.archEval ℚ Rat.infinitePlace (AdelicLevel.adeleArch (𝓞 ℚ) ℚ (v i))‖ ≤ M') :
    (((archPlaceComponent3 ℚ Rat.infinitePlace ((n * t * k)⁻¹ * radicalP21 v * (n * t * k)) :
            Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) - 1) *
          ((archPlaceComponent3 ℚ Rat.infinitePlace ((n * t * k)⁻¹ * radicalP21 v * (n * t * k)) :
            Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) - 1) = 0 ∧
        ∀ i j : Fin 3,
          ‖((archPlaceComponent3 ℚ Rat.infinitePlace ((n * t * k)⁻¹ * radicalP21 v * (n * t * k)) :
              Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) - 1) i j‖ ≤
            2 * (1 + C) * max 1 c⁻¹ * M' / archRoot₂ ℚ Rat.infinitePlace t) ∧
    (((archPlaceComponent3 ℚ Rat.infinitePlace ((n * t * k)⁻¹ * radicalP12 v * (n * t * k)) :
            Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) - 1) *
          ((archPlaceComponent3 ℚ Rat.infinitePlace ((n * t * k)⁻¹ * radicalP12 v * (n * t * k)) :
            Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) - 1) = 0 ∧
        ∀ i j : Fin 3,
          ‖((archPlaceComponent3 ℚ Rat.infinitePlace ((n * t * k)⁻¹ * radicalP12 v * (n * t * k)) :
              Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) - 1) i j‖ ≤
            2 * (1 + C) * max 1 c⁻¹ * M' / archRoot₁ ℚ Rat.infinitePlace t) := by sorry
