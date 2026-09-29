-- Prove2me | Theorems.Thm_NumberField_AdelicHeight_neg_log_adelicHeight_sub_log_adelicHeight_adelicWeyl_mul_eq_unipotentGL2_of_mem_adelicBorel
-- name    : NumberField.AdelicHeight.neg_log_adelicHeight_sub_log_adelicHeight_adelicWeyl_mul_eq_unipotentGL2_of_mem_adelicBorel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/c22bf41e-6cf6-5179-912c-f40657b0c005
-- title:
--   Adelic height weight of bk depends only on its unipotent coordinate
-- statement:
--   Let $F$ be a number field, write $\mathbb{A} =$ `AdeleRing (𝓞 F) F`, and let $b,k$ be elements of `AdelicGL2 (𝓞 F) F` $= \mathrm{GL}_2(\mathbb{A})$. Assume $b$ lies in `adelicBorel (𝓞 F) F`, i.e. its $(1,0)$ matrix entry vanishes, and $k$ lies in `adelicMaximalCompact F`, i.e. the finite component of $k$ lies in `finiteIntegralGL2 (𝓞 F) F` and, at every infinite place $w$ of $F$, the component of $k$ at $w$ satisfies `IsRowIsometry`: its determinant has absolute value $1$ and the map $(x,y)\mapsto (x k_{00} + y k_{10},\, x k_{01} + y k_{11})$ preserves $\|x\|^2+\|y\|^2$. Let $H$ denote `adelicHeight F`, the product of `archHeight F` of the archimedean component (a product of local heights over the infinite places, each raised to the multiplicity of the place) with `finHeight F` of the finite component (a finitary product of local heights over `HeightOneSpectrum (𝓞 F)`), and let $w$ be `adelicWeyl (𝓞 F) F`, the image in $\mathrm{GL}_2(\mathbb{A})$ of the antidiagonal matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ over $F$. Put $x = b_{01}\cdot u^{-1}$, where $u$ is the unit `borelDiagFst ⟨b, hb⟩` of $\mathbb{A}$ with underlying element $b_{00}$, and let $n(x) =$ `unipotentGL2 x` $= \begin{pmatrix}1&x\\0&1\end{pmatrix}$. Then $$-\log H(bk) - \log H(w\,(bk)) = -\log H(n(x)) - \log H(w\,n(x)).$$
--
--   The expression $-\log H(g) - \log H(wg)$ is the height weight attached to $g$ and its Weyl translate; the statement says that on the big cell this weight, evaluated on a Borel element times an element of the maximal compact subgroup, depends only on the unipotent coordinate $x = b_{01}/b_{00}$, the diagonal contributions cancelling between the two terms. It feeds the support-excursion bound [`AutomorphicForm.exists_forall_abs_log_adelicHeight_mul_adelicHeight_adelicWeyl_le_mul_prod_pow_log_measure_of_doubleCoset_apply_ne_zero`](thm.html#AutomorphicForm.exists_forall_abs_log_adelicHeight_mul_adelicHeight_adelicWeyl_le_mul_prod_pow_log_measure_of_doubleCoset_apply_ne_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicHeight_neg_log_adelicHeight_sub_log_adelicHeight_adelicWeyl_mul_eq_unipotentGL2_of_mem_adelicBorel.lean

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

theorem NumberField.AdelicHeight.neg_log_adelicHeight_sub_log_adelicHeight_adelicWeyl_mul_eq_unipotentGL2_of_mem_adelicBorel
    (F : Type) [Field F] [NumberField F]
    (b k : AdelicGL2 (𝓞 F) F) (hb : b ∈ adelicBorel (𝓞 F) F) (hk : k ∈ adelicMaximalCompact F) :
    -Real.log (NumberField.AdelicHeight.adelicHeight F (b * k))
        - Real.log (NumberField.AdelicHeight.adelicHeight F (AutomorphicForm.adelicWeyl (𝓞 F) F * (b * k))) =
      -Real.log (NumberField.AdelicHeight.adelicHeight F
          (unipotentGL2 ((b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1 *
            ((borelDiagFst ⟨b, hb⟩)⁻¹ : (AdeleRing (𝓞 F) F)ˣ))))
        - Real.log (NumberField.AdelicHeight.adelicHeight F (AutomorphicForm.adelicWeyl (𝓞 F) F *
          unipotentGL2 ((b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1 *
            ((borelDiagFst ⟨b, hb⟩)⁻¹ : (AdeleRing (𝓞 F) F)ˣ)))) := by sorry
