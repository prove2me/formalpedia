-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_mul_dual_eq_of_isGL3PsiWhittakerFn_inv_of_unipotent
-- name    : LanglandsTunnell.CubicInduction.mul_dual_eq_of_isGL3PsiWhittakerFn_inv_of_unipotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/6ab0c9fe-2da3-5852-adfe-ffb0b1d5be1a
-- title:
--   Unipotent invariance of the dual Rankin–Selberg integrand
-- statement:
--   Let $v$ be a height-one prime of $\mathbb{Z} = \mathcal{O}_{\mathbb{Q}}$, with completion $\mathbb{Q}_v$, and let $\psi_v$ be a complex additive character of $\mathbb{Q}_v$ assumed equal to the inverse of the standard local character $\psi_{\mathbb{Q},v} =$ [`NumberField.StandardAddChar.psiLocal ℚ v`](def/LanglandsTunnell_StandardLocalConstantsAt.html#L65) (the standard adelic additive character of $\mathbb{Q}$ precomposed with the inclusion of $\mathbb{Q}_v$ into the adeles at $v$). Let $F \colon \mathrm{GL}_3(\mathbb{Q}_v) \to \mathbb{C}$ satisfy `IsGL3PsiWhittakerFn` for the character $\psi_v^{-1}$, i.e. $F(u(x,y,z)g) = \psi_v^{-1}(x+y)\,F(g)$ for all $x,y,z \in \mathbb{Q}_v$ and all $g$, where $u(x,y,z)$ is the upper unipotent matrix with rows $(1,x,z)$, $(0,1,y)$, $(0,0,1)$. Let $W_2 \colon \mathrm{GL}_2(\mathbb{Q}_v) \to \mathbb{C}$ satisfy $W_2(n(x)g) = \psi_{\mathbb{Q},v}(x)\,W_2(g)$ for all $x$ and $g$, where $n(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$. Then for all $x \in \mathbb{Q}_v$, all $X \in \mathrm{GL}_3(\mathbb{Q}_v)$ and all $h \in \mathrm{GL}_2(\mathbb{Q}_v)$,
--   $$F(\iota(n(x))X)\,W_2\bigl(w\,{}^{t}(n(x)h)^{-1}\bigr) = F(X)\,W_2\bigl(w\,{}^{t}h^{-1}\bigr),$$
--   where $\iota$ is the block embedding $\mathrm{GL}_2 \to \mathrm{GL}_3$ sending $M$ to $\mathrm{diag}(M,1)$, $w = \begin{pmatrix}0&1\\1&0\end{pmatrix}$, and ${}^{t}g^{-1}$ denotes the transpose of the inverse.
--
--   This is the invariance of the dual local Rankin–Selberg integrand for $\mathrm{GL}_3 \times \mathrm{GL}_2$ under the unipotent line: the two Whittaker phases, one from the $\mathrm{GL}_3$ function along the embedded unipotent and one from the $\mathrm{GL}_2$ partner in its dual argument, are inverse to each other. It is used in the construction of the dual local integrals, in the integrability statement for the dual integrand and in the evaluation of the local Rankin–Selberg integral of the cubic-induction Whittaker function in a fixed chamber.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_mul_dual_eq_of_isGL3PsiWhittakerFn_inv_of_unipotent.lean

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

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
open scoped nonZeroDivisors

theorem LanglandsTunnell.CubicInduction.mul_dual_eq_of_isGL3PsiWhittakerFn_inv_of_unipotent
    (v : HeightOneSpectrum (𝓞 ℚ))
    (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (hψinv : ψv = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹)
    (F : LocalGL3 v → ℂ) (hF : IsGL3PsiWhittakerFn ψv⁻¹ F)
    (W₂ : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (hW₂ψ : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
      W₂ (UnramifiedWhittaker.unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ v x * W₂ g)
    (x : v.adicCompletion ℚ) (X : LocalGL3 v) (h : GL (Fin 2) (v.adicCompletion ℚ)) :
    F (iotaGL (UnramifiedWhittaker.unipotent x) * X) *
        W₂ ((AutomorphicForm.gl2Weyl : GL (Fin 2) (v.adicCompletion ℚ)) *
          AutomorphicForm.transposeInvN (Fin 2) (UnramifiedWhittaker.unipotent x * h)) =
      F X *
        W₂ ((AutomorphicForm.gl2Weyl : GL (Fin 2) (v.adicCompletion ℚ)) *
          AutomorphicForm.transposeInvN (Fin 2) h) := by sorry
