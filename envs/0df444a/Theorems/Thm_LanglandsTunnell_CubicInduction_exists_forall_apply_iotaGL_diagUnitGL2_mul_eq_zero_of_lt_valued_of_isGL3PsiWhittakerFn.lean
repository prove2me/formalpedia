-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_apply_iotaGL_diagUnitGL2_mul_eq_zero_of_lt_valued_of_isGL3PsiWhittakerFn
-- name    : LanglandsTunnell.CubicInduction.exists_forall_apply_iotaGL_diagUnitGL2_mul_eq_zero_of_lt_valued_of_isGL3PsiWhittakerFn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/d991cc6b-1221-5c29-a774-1d1d00f6f9b0
-- title:
--   Torus line of a smooth Whittaker function on GL₃ vanishes for large |a|
-- statement:
--   Let $v$ be a nonzero prime ideal of the ring of integers of $\mathbb{Q}$, let $\psi_v$ be an additive character of the $v$-adic completion $\mathbb{Q}_v$ of $\mathbb{Q}$ with $\psi_v \neq 1$, and let $W : GL_3(\mathbb{Q}_v) \to \mathbb{C}$ be a function satisfying `IsGL3PsiWhittakerFn` for $\psi_v$, i.e. $W(\mathrm{u}(x,y,z)\,g) = \psi_v(x+y)\,W(g)$ for all $x,y,z \in \mathbb{Q}_v$ and all $g \in GL_3(\mathbb{Q}_v)$, where $\mathrm{u}(x,y,z)$ is the upper triangular unipotent matrix with entries $x$ in position $(1,2)$, $y$ in position $(2,3)$ and $z$ in position $(1,3)$. Assume further that $W$ is smooth in the sense that there is a subgroup $U_v$ of $GL_3(\mathbb{Q}_v)$, open as a subset, with $W(gk) = W(g)$ for all $k \in U_v$ and all $g$. Then for each fixed $g \in GL_3(\mathbb{Q}_v)$ there exists an integer $K$ such that $W(\mathrm{diag}(a,1,1)\,g) = 0$ for every unit $a$ of $\mathbb{Q}_v$ whose value $\mathrm{v}(a)$ in $\mathbb{Z}_{m0}$ exceeds $\exp K$; here $\mathrm{diag}(a,1,1)$ is the image under the block embedding `iotaGL` of the $GL_2$ element $\mathrm{diag}(a,1)$.
--
--   This is the standard support bound for a smooth Whittaker function restricted to the torus line $a \mapsto W(\mathrm{diag}(a,1,1)g)$: the function vanishes once $|a|_v$ is large, the bound depending on $g$ and on the open subgroup of right invariance. It feeds the shell decomposition used in the non-vanishing statement for the local $GL_3 \times GL_1$ zeta integrals, [`LanglandsTunnell.CubicInduction.exists_isLocalZeta30ConvergentAbove_and_forall_exists_localZeta30_ne_zero_of_admissible_of_ne_zero`](thm.html#LanglandsTunnell.CubicInduction.exists_isLocalZeta30ConvergentAbove_and_forall_exists_localZeta30_ne_zero_of_admissible_of_ne_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_forall_apply_iotaGL_diagUnitGL2_mul_eq_zero_of_lt_valued_of_isGL3PsiWhittakerFn.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal MeasureTheory
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.exists_forall_apply_iotaGL_diagUnitGL2_mul_eq_zero_of_lt_valued_of_isGL3PsiWhittakerFn
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ) (hψv : ψv ≠ 1)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψv W)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (g : LocalGL3 v) :
    ∃ K : ℤ, ∀ a : (v.adicCompletion ℚ)ˣ, WithZero.exp K < Valued.v (a : v.adicCompletion ℚ) →
      W (iotaGL (diagUnitGL2 a) * g) = 0 := by sorry
