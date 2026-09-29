-- Prove2me | Theorems.Thm_NumberField_InfinitePlace_Completion_exists_forall_apply_eq_cpow_of_extensionEmbedding_eq_of_continuous
-- name    : NumberField.InfinitePlace.Completion.exists_forall_apply_eq_cpow_of_extensionEmbedding_eq_of_continuous
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/c551b8dd-d293-55c1-907e-8f68e265091f
-- title:
--   Continuous quasi-characters of F_w^× as powers on positive reals
-- statement:
--   Let $F$ be a field, $w$ an infinite place of $F$ in the sense of Mathlib (an absolute value on $F$ arising as $|\varphi(\cdot)|$ for some ring homomorphism $\varphi \colon F \to \mathbb{C}$), and let $w.\mathrm{Completion}$ be the completion of $F$ at $w$, equipped with the ring homomorphism $\mathtt{extensionEmbedding}\ w \colon w.\mathrm{Completion} \to \mathbb{C}$ obtained by extending the embedding attached to $w$ by continuity. Let $\chi$ be a homomorphism of monoids from the unit group $(w.\mathrm{Completion})^\times$ to $\mathbb{C}^\times$, and assume that the function $x \mapsto \chi(x) \in \mathbb{C}$ obtained by composing $\chi$ with the inclusion $\mathbb{C}^\times \hookrightarrow \mathbb{C}$ is continuous. Then there is a complex number $s$ with the following two properties. First, for every unit $u$ of $w.\mathrm{Completion}$ and every real $r > 0$ such that $\mathtt{extensionEmbedding}\ w\,(u) = r$ in $\mathbb{C}$, one has $\chi(u) = r^{s}$, the complex power of the positive real $r$. Second, if $\chi$ is unitary, that is $\|\chi(u)\| = 1$ for all units $u$, then $\operatorname{Re} s = 0$. Note that the first clause constrains $\chi$ only on those units whose image in $\mathbb{C}$ is a positive real number.
--
--   This is the archimedean part of Tate's description of the quasi-characters of a local field, namely that such a character agrees with a complex power of the absolute value on the positive reals, purely imaginary exponent in the unitary case. It is used in the evaluation of archimedean local zeta integrals of Gaussians against $\chi$ as Gamma factors, in [`AutomorphicForm.exists_localZeta_line_eq_mul_GammaReal_mul_of_bihomogeneous_mul_gaussian`](thm.html#AutomorphicForm.exists_localZeta_line_eq_mul_GammaReal_mul_of_bihomogeneous_mul_gaussian).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_InfinitePlace_Completion_exists_forall_apply_eq_cpow_of_extensionEmbedding_eq_of_continuous.lean

import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion

theorem NumberField.InfinitePlace.Completion.exists_forall_apply_eq_cpow_of_extensionEmbedding_eq_of_continuous
    (F : Type) [Field F] (w : InfinitePlace F)
    (χ : (w.Completion)ˣ →* ℂˣ)
    (_hχc : Continuous fun x : (w.Completion)ˣ => ((χ x : ℂˣ) : ℂ)) :
    ∃ s : ℂ,
      (∀ (u : (w.Completion)ˣ) (r : ℝ), 0 < r → extensionEmbedding w (u : w.Completion) = (r : ℂ) →
        ((χ u : ℂˣ) : ℂ) = (r : ℂ) ^ s) ∧
      ((∀ u : (w.Completion)ˣ, ‖((χ u : ℂˣ) : ℂ)‖ = 1) → s.re = 0) := by sorry
