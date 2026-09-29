-- Prove2me | Theorems.Thm_NumberField_AdelicHeight_neg_log_adelicHeight_sub_log_adelicHeight_adelicWeyl_mul_diagonal_mul_and_continuous
-- name    : NumberField.AdelicHeight.neg_log_adelicHeight_sub_log_adelicHeight_adelicWeyl_mul_diagonal_mul_and_continuous
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/63d3e4a1-cae6-5b80-a5bd-f7c220345180
-- title:
--   Diagonal invariance and continuity of the adelic height weight
-- statement:
--   Let $F$ be a number field. The assertion is a conjunction of two statements about the function $W(g) = -\log \mathrm{adelicHeight}_F(g) - \log \mathrm{adelicHeight}_F(w_0 g)$ on the group $\mathrm{AdelicGL2}(\mathcal{O}_F, F) = \mathrm{GL}_2(\mathbb{A}_F)$ of invertible $2 \times 2$ matrices over the adele ring, where $\mathrm{adelicHeight}_F(g)$ is the product of $\mathrm{archHeight}_F$ of the infinite-adelic component $\mathrm{glArch}(g)$, itself the product over the infinite places $v$ of $F$ of the local height of the $v$-component raised to the power $v.\mathrm{mult}$, with $\mathrm{finHeight}_F$ of the finite-adelic component $\mathrm{glFin}(g)$, itself the finitary product over $v$ in the height one spectrum of $\mathcal{O}_F$ of the local finite heights of the $v$-components; and where $w_0 = \mathrm{adelicWeyl}(\mathcal{O}_F, F)$ is the image in $\mathrm{GL}_2(\mathbb{A}_F)$, under the map induced by $F \to \mathbb{A}_F$, of the antidiagonal matrix $\begin{pmatrix} 0 & 1 \\ 1 & 0\end{pmatrix} \in \mathrm{GL}_2(F)$. First: for every $h \in \mathrm{GL}_2(\mathbb{A}_F)$ whose underlying matrix has vanishing off-diagonal entries, $h_{1 0} = 0$ and $h_{0 1} = 0$, and every $g \in \mathrm{GL}_2(\mathbb{A}_F)$, one has $W(hg) = W(g)$. Second: $W$ is continuous on $\mathrm{GL}_2(\mathbb{A}_F)$.
--
--   The function $W$ is the logarithmic weight attached to the adelic height on $\mathrm{GL}_2(\mathbb{A}_F)$, and the two clauses record that it is left-invariant under the diagonal torus and continuous, so that it descends to a continuous weight on the relevant quotients. It is used in the treatment of orbital and twisted orbital integrals over quotients by the centre, being cited by the statements identifying such integrals with integrals over the Haar quotient.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicHeight_neg_log_adelicHeight_sub_log_adelicHeight_adelicWeyl_mul_diagonal_mul_and_continuous.lean

import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_AdelicLsXi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem NumberField.AdelicHeight.neg_log_adelicHeight_sub_log_adelicHeight_adelicWeyl_mul_diagonal_mul_and_continuous
    (F : Type) [Field F] [NumberField F] :
    (∀ (h : AdelicGL2 (𝓞 F) F),
      (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 = 0 →
      (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1 = 0 →
      ∀ g : AdelicGL2 (𝓞 F) F,
        -Real.log (NumberField.AdelicHeight.adelicHeight F (h * g))
            - Real.log (NumberField.AdelicHeight.adelicHeight F (AutomorphicForm.adelicWeyl (𝓞 F) F * (h * g))) =
          -Real.log (NumberField.AdelicHeight.adelicHeight F g)
            - Real.log (NumberField.AdelicHeight.adelicHeight F (AutomorphicForm.adelicWeyl (𝓞 F) F * g))) ∧
    Continuous (fun g : AdelicGL2 (𝓞 F) F =>
      -Real.log (NumberField.AdelicHeight.adelicHeight F g)
        - Real.log (NumberField.AdelicHeight.adelicHeight F (AutomorphicForm.adelicWeyl (𝓞 F) F * g))) := by sorry
