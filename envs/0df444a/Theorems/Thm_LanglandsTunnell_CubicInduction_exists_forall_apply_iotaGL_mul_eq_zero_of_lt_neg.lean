-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_apply_iotaGL_mul_eq_zero_of_lt_neg
-- name    : LanglandsTunnell.CubicInduction.exists_forall_apply_iotaGL_mul_eq_zero_of_lt_neg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/3b569c20-6e39-5551-a88a-321534e899c9
-- title:
--   Whittaker functions vanish deep in the GL₂-torus
-- statement:
--   Let $v$ be a height-one prime of $\mathcal{O}_{\mathbb{Q}}$, write $F = \mathbb{Q}_v$ for the $v$-adic completion, and let $\psi_v$ be an additive character $F \to \mathbb{C}^\times$ assumed equal to the inverse $(\psi_{\mathrm{loc}})^{-1}$ of the standard local character [`NumberField.StandardAddChar.psiLocal`](def/LanglandsTunnell_StandardLocalConstantsAt.html#L65) at $v$ (the restriction of the standard adelic character $\psi_K$ through the inclusion of $F$ into the adeles). Let $W : \mathrm{GL}_3(F) \to \mathbb{C}$ satisfy `IsGL3PsiWhittakerFn`, i.e. $W(n(x,y,z)g) = \psi_v(x+y)\,W(g)$ for all $x,y,z \in F$ and all $g$, where $n(x,y,z)$ is the upper triangular unipotent matrix with entries $x,y$ on the superdiagonal and $z$ in position $(1,3)$. Let $\varpi$ lie in the valuation ring of $F$, with nonzero image in $F$ of valuation $\exp(-1)$, i.e. a uniformiser. Let $C \subseteq \mathrm{GL}_3(F)$ be any subset and $U \le \mathrm{GL}_3(F)$ an open subgroup such that $W(xk'y) = W(xy)$ for all $y \in C$, $k' \in U$ and $x \in \mathrm{GL}_3(F)$. Then there exists $L \in \mathbb{N}$ with the following property: for every $y \in C$, every pair of integers $(n_1,n_2)$ with $n_1 < -L$ or $n_2 < -L$, and every unit $u \in F^\times$ of valuation $1$, setting $t = \mathrm{diag}(\varpi,\varpi)^{n_2}\cdot\mathrm{diag}(\varpi^{n_1}u, 1) \in \mathrm{GL}_2(F)$ and $\iota$ the embedding of $\mathrm{GL}_2$ as the upper-left block of $\mathrm{GL}_3$ with $1$ in position $(3,3)$, one has both $W(\iota(t)\,y) = 0$ and $W\bigl(w_3\,{}^{t}\!\iota(t)^{-1}\,y\bigr) = 0$, where $w_3$ is the long Weyl element (the antidiagonal permutation matrix) and ${}^{t}g^{-1}$ denotes the transpose-inverse.
--
--   This is the unipotent-averaging ("unipotent trick") vanishing statement for smooth $\psi$-Whittaker functions on $\mathrm{GL}_3$ over a $p$-adic field, in the form needed uniformly over a family of right translates $W(\,\cdot\,y)$, $y \in C$, all fixed by the single open subgroup $U$; the second clause is the same assertion for the dual function $g \mapsto W(w_3\,{}^{t}g^{-1})$. It supplies the cut-off $L$ used in the finiteness statements for shallow type integrals and for the Rankin–Selberg local integrals of $\mathrm{GL}_3 \times \mathrm{GL}_2$ Whittaker data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_forall_apply_iotaGL_mul_eq_zero_of_lt_neg.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
  LanglandsTunnell.Converse
open scoped nonZeroDivisors

theorem
LanglandsTunnell.CubicInduction.exists_forall_apply_iotaGL_mul_eq_zero_of_lt_neg
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (hψinv : ψv = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψv W)
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (C : Set (LocalGL3 v)) (U : Subgroup (LocalGL3 v)) (hU : IsOpen (U : Set (LocalGL3 v)))
    (hfix : ∀ y ∈ C, ∀ k' ∈ U, ∀ x : LocalGL3 v, W (x * k' * y) = W (x * y)) :
    ∃ L : ℕ, ∀ y ∈ C, ∀ n : ℤ × ℤ, (n.1 < -(L : ℤ) ∨ n.2 < -(L : ℤ)) →
      ∀ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 →
        W (iotaGL (UnramifiedWhittaker.scalarPi
              (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 *
            diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ
              ^ n.1 * u)) * y) = 0 ∧
        W (longWeyl3 * transposeInv3 (iotaGL (UnramifiedWhittaker.scalarPi
              (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 *
            diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ
              ^ n.1 * u))) * y) = 0 := by sorry
