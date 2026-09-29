-- Prove2me | Theorems.Thm_NumberField_AdelicHeight_neg_log_adelicHeight_unipotentGL2_sub_log_adelicHeight_adelicWeyl_mul_unipotentGL2_eq
-- name    : NumberField.AdelicHeight.neg_log_adelicHeight_unipotentGL2_sub_log_adelicHeight_adelicWeyl_mul_unipotentGL2_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/821f57d5-0b16-5a4b-886f-9e0b189f9cdd
-- title:
--   Adelic heights of a unipotent and its Weyl translate
-- statement:
--   Let $F$ be a number field and let $x$ be an adele of $F$, written as a pair $x = (x_1, x_2)$ with $x_1$ in the infinite adeles and $x_2$ in the finite adeles of the ring of integers $\mathcal{O}_F$. Write $n(x)$ for `unipotentGL2 x`, the element of $\mathrm{GL}_2$ of the adele ring with matrix $\begin{pmatrix}1 & x\\ 0 & 1\end{pmatrix}$ (inverse $\begin{pmatrix}1 & -x\\ 0 & 1\end{pmatrix}$), and $w$ for `adelicWeyl`, the image under the map induced by $F \to \mathbb{A}_F$ of the global matrix $\begin{pmatrix}0 & 1\\ 1 & 0\end{pmatrix}$. Here the adelic height of $g \in \mathrm{GL}_2(\mathbb{A}_F)$ is the product of its archimedean height $\prod_{w \mid \infty} \mathrm{localHeight}(g_w)^{m_w}$, with $m_w$ the multiplicity of the infinite place $w$, and of its finite height $\prod^{\mathrm{f}}_{v} \mathrm{finLocalHeight}(g_v)$, a finitely supported product over the height one primes $v$ of $\mathcal{O}_F$, the local factors being the project's functions `localHeight` and `finLocalHeight` applied to the components of $g$. The theorem asserts the identity $$-\log H(n(x)) - \log H(w\,n(x)) \;=\; \sum_{w \mid \infty} m_w \log\bigl(1 + \lVert x_1(w)\rVert^2\bigr) \;+\; 2 \sum^{\mathrm{f}}_{v} \log \max\bigl(1, \lVert x_2(v)\rVert\bigr),$$ where the first sum is the finite sum over the infinite places of $F$ and the second is a finitely supported sum over the height one primes of $\mathcal{O}_F$.
--
--   This is the explicit evaluation of the combined height functional $-\log H(n) - \log H(wn)$ along the unipotent horocycle, expressing it as a sum of local contributions of the coordinate $x$. It is used in the proof of the excursion bound [`AutomorphicForm.exists_forall_abs_log_adelicHeight_mul_adelicHeight_adelicWeyl_le_mul_prod_pow_log_measure_of_doubleCoset_apply_ne_zero`](thm.html#AutomorphicForm.exists_forall_abs_log_adelicHeight_mul_adelicHeight_adelicWeyl_le_mul_prod_pow_log_measure_of_doubleCoset_apply_ne_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicHeight_neg_log_adelicHeight_unipotentGL2_sub_log_adelicHeight_adelicWeyl_mul_unipotentGL2_eq.lean

import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm

theorem NumberField.AdelicHeight.neg_log_adelicHeight_unipotentGL2_sub_log_adelicHeight_adelicWeyl_mul_unipotentGL2_eq
    (F : Type) [Field F] [NumberField F] (x : AdeleRing (𝓞 F) F) :
    -Real.log (NumberField.AdelicHeight.adelicHeight F (unipotentGL2 x))
        - Real.log (NumberField.AdelicHeight.adelicHeight F (AutomorphicForm.adelicWeyl (𝓞 F) F * unipotentGL2 x)) =
      (∑ w : InfinitePlace F, (w.mult : ℝ) * Real.log (1 + ‖x.1 w‖ ^ 2)) +
        2 * ∑ᶠ v : HeightOneSpectrum (𝓞 F), Real.log (max 1 ‖x.2 v‖) := by sorry
