-- Prove2me | Theorems.Thm_NumberField_AdelicHeight_adelicHeight_unipotentGL2_mul_and_centralScalar_mul
-- name    : NumberField.AdelicHeight.adelicHeight_unipotentGL2_mul_and_centralScalar_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/281e37ae-59ef-5658-a50f-f0fd3c626d55
-- title:
--   Left unipotent and central invariance of the adelic height
-- statement:
--   Let $F$ be a number field. Write $\mathbb{A}_F$ for the adele ring of $F$ (relative to $\mathcal{O}_F$) and $\mathrm{AdelicGL2}$ for $\mathrm{GL}_2(\mathbb{A}_F)$, and let $H =$ `adelicHeight F` be the function on $\mathrm{GL}_2(\mathbb{A}_F)$ defined as the product of the archimedean factor `archHeight F` evaluated at the image of $g$ under the entrywise map $\mathbb{A}_F \to \mathbb{A}_{F,\infty}$ — that is, $\prod_{v \mid \infty} \mathrm{localHeight}(g_v)^{\mathrm{mult}(v)}$ over the infinite places, with $g_v$ the component of $g$ at $v$ — and the finite factor `finHeight F` evaluated at the image of $g$ under the entrywise map to $\mathrm{GL}_2$ of the finite adele ring, namely the (finitely supported) product $\prod_{v} \mathrm{finLocalHeight}(g_v)$ over the height-one primes $v$ of $\mathcal{O}_F$. The theorem asserts the conjunction of two invariance statements: first, for every adele $x \in \mathbb{A}_F$ and every $g \in \mathrm{GL}_2(\mathbb{A}_F)$, $H\bigl(n(x)g\bigr) = H(g)$, where $n(x)$ is the invertible matrix $\begin{pmatrix} 1 & x \\ 0 & 1\end{pmatrix}$ with inverse $\begin{pmatrix} 1 & -x \\ 0 & 1\end{pmatrix}$; and second, for every idele $z \in \mathbb{A}_F^{\times}$ and every $g$, $H\bigl(z I_2 \cdot g\bigr) = H(g)$, where $z I_2$ is the central scalar element $\mathrm{scalar}(z)$ of $\mathrm{GL}_2(\mathbb{A}_F)$.
--
--   These are the two basic invariance properties of the height function used in adelic reduction theory for $\mathrm{GL}_2$: the height is a function on $Z(\mathbb{A}_F)N(\mathbb{A}_F)\backslash \mathrm{GL}_2(\mathbb{A}_F)$. They are used throughout the analytic part of the development, for instance in the estimates for pseudo-Eisenstein series supported on a Siegel slab, in the transversal measure computations, and in the constant-term analysis on twisted Bruhat cells.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicHeight_adelicHeight_unipotentGL2_mul_and_centralScalar_mul.lean

import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_AdelicLsXi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AutomorphicForm NumberField

theorem NumberField.AdelicHeight.adelicHeight_unipotentGL2_mul_and_centralScalar_mul
    (F : Type) [Field F] [NumberField F] :
    (∀ (x : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F),
        adelicHeight F (unipotentGL2 x * g) = adelicHeight F g) ∧
      ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
        adelicHeight F (centralScalar (𝓞 F) F z * g) = adelicHeight F g := by sorry
