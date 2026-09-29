-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_WhittakerBlock_norm_sub_le_sum_abs_mul_of_mul_self_eq_zero_of_archDeriv_le
-- name    : LanglandsTunnell.CubicInduction.WhittakerBlock.norm_sub_le_sum_abs_mul_of_mul_self_eq_zero_of_archDeriv_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/0882ff38-5c21-509c-a87a-43aca8fb476f
-- title:
--   Mean-value bound along a square-zero direction in GL₃(A_ℚ)
-- statement:
--   Let $F$ be a complex-valued function on $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$, the group of invertible $3\times 3$ matrices over the adele ring of $\mathbb{Q}$, and assume `IsArchSmooth3 F`: for every $g$ the map $e \mapsto F(g\cdot \mathrm{archRealLift3}(e))$ from real $3\times 3$ arrays to $\mathbb{C}$ is $C^\infty$ on the open set where $\det e \neq 0$, where $\mathrm{archRealLift3}(e)$ denotes the adelic matrix obtained from $e$ by the archimedean inclusion, regarded as an element of $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ when it is a unit and as $1$ otherwise. Let $x \in \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$, let $e$ be a real $3\times 3$ array with $\det e \neq 0$, let $Y$ be a real $3\times 3$ matrix with $Y\cdot Y = 0$, and let $B$ be a real number bounding, for all $s \in [0,1]$ and all $i,j \in \{0,1,2\}$, the norm of $(\mathrm{archDeriv}\ i\ j\ F)\bigl(x\cdot \mathrm{archRealLift3}((1+sY)e)\bigr)$, where $\mathrm{archDeriv}\ i\ j\ F$ at a point $g$ is the derivative at $s=0$ of $s \mapsto F\bigl(g\cdot\mathrm{archRealLift3}(1 + sE_{ij})\bigr)$, $E_{ij}$ the elementary matrix. Then $$\bigl\|F(x\cdot\mathrm{archRealLift3}(e)) - F\bigl(x\cdot\mathrm{archRealLift3}((1+Y)e)\bigr)\bigr\| \le \Bigl(\sum_{i,j} \bigl|(e^{-1}Ye)_{ij}\bigr|\Bigr)\, B.$$
--
--   This is the mean-value inequality applied along the segment $s \mapsto (1+sY)e$ of invertible real arrays, in the form needed for archimedean displacement estimates: since $Y^2 = 0$, the logarithmic direction $((1+sY)e)^{-1}Ye = e^{-1}Ye$ is independent of $s$, so the nine right-invariant derivatives $\mathrm{archDeriv}\ i\ j$ control the increment of $F$ with constant coefficients. It is the calculus input to [`LanglandsTunnell.CubicInduction.exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel`](thm.html#LanglandsTunnell.CubicInduction.exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel), the decay estimate for functions on Siegel sets.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_WhittakerBlock_norm_sub_le_sum_abs_mul_of_mul_self_eq_zero_of_archDeriv_le.lean

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

open LanglandsTunnell.CubicInduction.WhittakerBlock (archDeriv)

theorem LanglandsTunnell.CubicInduction.WhittakerBlock.norm_sub_le_sum_abs_mul_of_mul_self_eq_zero_of_archDeriv_le
    (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : WhittakerBlock.IsArchSmooth3 F) (x : AdelicGL 3 (𝓞 ℚ) ℚ)
    (e : Fin 3 → Fin 3 → ℝ) (he : (Matrix.of e).det ≠ 0)
    (Y : Matrix (Fin 3) (Fin 3) ℝ) (hY : Y * Y = 0) (B : ℝ)
    (hB : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ i j : Fin 3,
      ‖archDeriv i j F (x * WhittakerBlock.archRealLift3 (fun a b => ((1 + s • Y) * Matrix.of e) a b))‖ ≤ B) :
    ‖F (x * WhittakerBlock.archRealLift3 e) -
        F (x * WhittakerBlock.archRealLift3 (fun a b => ((1 + Y) * Matrix.of e) a b))‖ ≤
      (∑ i : Fin 3, ∑ j : Fin 3, |((Matrix.of e)⁻¹ * Y * Matrix.of e) i j|) * B := by sorry
