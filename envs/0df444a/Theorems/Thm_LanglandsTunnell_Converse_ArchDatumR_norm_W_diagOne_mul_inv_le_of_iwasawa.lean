-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_ArchDatumR_norm_W_diagOne_mul_inv_le_of_iwasawa
-- name    : LanglandsTunnell.Converse.ArchDatumR.norm_W_diagOne_mul_inv_le_of_iwasawa
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/d26ff62c-fe72-5c86-ba00-93666bae9c6a
-- title:
--   Iwasawa bound for W_D(diag(at,1)e⁻¹)
-- statement:
--   Let $P_2$ be a real archimedean parameter, let $D$ be an archimedean datum of parameter $P_2$ — in particular a function $W = D.W$ on real $2\times 2$ matrices with values in $\mathbb{C}$ satisfying the unipotent and central transformation laws and the two decay laws `decay_top`, `decay_zero` of `ArchDatumR` — and let $a$ be a nonzero real number. The assertion is that for every natural number $N$ there are real constants $C \ge 0$ and $\sigma_0 \ge 0$ such that for all real $t$ and all real $2\times 2$ matrices $e$ with $t \neq 0$ and $\det e \neq 0$, writing $\rho^2 = \sum_i (e^{-1})_{1i}^2$ for the squared length of the second row of $e^{-1}$ and $r = |at|/(|\det e|\,\rho^2)$, one has $$\bigl\| W\bigl(\mathrm{diag}(at,1)\, e^{-1}\bigr)\bigr\| \le C\,\rho^{\,\mathrm{Re}\,c(P_2)+1}\bigl(r^{-N} + r^{-\sigma_0}\bigr),$$ where $\mathrm{diag}(y,1)$ is the matrix $\begin{pmatrix} y & 0\\ 0 & 1\end{pmatrix}$, $c(P_2)$ is the central exponent of $P_2$ (equal to $u_1+u_2$ in the principal case and $2u$ in the discrete case), and the powers of $\rho$ and $r$ are real powers. The constants $C$ and $\sigma_0$ depend on $D$ and $N$ only, not on $t$ or $e$.
--
--   This is the standard Iwasawa-coordinate estimate for an archimedean Whittaker function on $GL_2(\mathbb{R})$ along the torus translate $\mathrm{diag}(at,1)e^{-1}$: the size is governed by the length of the second row of $e^{-1}$ through the central character, and by rapid decay for large $r$ together with a polynomial bound for small $r$. It feeds the Rankin–Selberg unfolding, where it is used to produce a dominating function for the unfolded torus pair integrand.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_ArchDatumR_norm_W_diagOne_mul_inv_le_of_iwasawa.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchWeightChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction LanglandsTunnell.CubicLambda MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open scoped Classical in

theorem LanglandsTunnell.Converse.ArchDatumR.norm_W_diagOne_mul_inv_le_of_iwasawa
    {P₂ : RealArchParam} (D : ArchDatumR P₂) (a : ℝ) (ha : a ≠ 0) :
    ∀ N : ℕ, ∃ C σ₀ : ℝ, 0 ≤ C ∧ 0 ≤ σ₀ ∧
      ∀ (t : ℝ) (e : Matrix (Fin 2) (Fin 2) ℝ), t ≠ 0 → e.det ≠ 0 →
        ‖D.W (ArchR.diagOne (a * t) * e⁻¹)‖ ≤
          C * Real.sqrt (∑ i, (e⁻¹ 1 i) ^ 2) ^ (P₂.centralExponent.re + 1) *
            ((|a * t| / (|e.det| * ∑ i, (e⁻¹ 1 i) ^ 2)) ^ (-(N : ℝ)) +
              (|a * t| / (|e.det| * ∑ i, (e⁻¹ 1 i) ^ 2)) ^ (-σ₀)) := by sorry
