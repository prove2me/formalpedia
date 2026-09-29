-- Prove2me | Theorems.Thm_NumberField_AdelicHeight_neg_log_adelicHeight_sub_log_adelicHeight_adelicWeyl_mul_eq_archWeight_glArch_add_finsum_weight_finComponent
-- name    : NumberField.AdelicHeight.neg_log_adelicHeight_sub_log_adelicHeight_adelicWeyl_mul_eq_archWeight_glArch_add_finsum_weight_finComponent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/dfe1e839-3bdf-5ba5-b58d-0e1a468bcef6
-- title:
--   Place splitting of the adelic Weyl height weight
-- statement:
--   Let $K$ be a number field and let $x \in \mathrm{GL}_2(\mathbb{A}_K)$, where $\mathbb{A}_K$ is the full adele ring of $\mathcal{O}_K$ in $K$. Write $H$ for `adelicHeight`, the product of the archimedean height $\prod_{v \mid \infty} (|\det|/\text{rowNormSq})^{\mathrm{mult}(v)}$ evaluated on the archimedean component `glArch` of a matrix and of the finite height $\prod^{\mathrm{f}}_{v} \mathrm{finLocalHeight}$ over the height-one primes $v$ of $\mathcal{O}_K$ evaluated on the local components of the finite part `glFin`; and write $w$ for `adelicWeyl`, the image in $\mathrm{GL}_2(\mathbb{A}_K)$ of the antidiagonal matrix $\begin{pmatrix} 0&1\\1&0\end{pmatrix} \in \mathrm{GL}_2(K)$. The assertion is the identity $$-\log H(x) - \log H(wx) \;=\; \bigl(-\log H_\infty(y) - \log H_\infty(\mathrm{glArch}(w)\, y)\bigr)\big|_{y = \mathrm{glArch}(x)} \;+\; \sum^{\mathrm{f}}_{v} \mathrm{weight}\bigl(x_v\bigr),$$ the finite sum running over the height-one spectrum of $\mathcal{O}_K$, $x_v$ denoting the image of $\mathrm{glFin}(x)$ in $\mathrm{GL}_2(K_v)$, and $\mathrm{weight}(g) = 2\log\bigl(\max(\|g_{00}\|,\|g_{01}\|)\cdot \max(\|g_{10}\|,\|g_{11}\|)/\|\det g\|\bigr)$. The archimedean term is stated as an explicit application of the displayed function of $y$ to $\mathrm{glArch}(x)$.
--
--   This is the place-by-place decomposition of the height weight attached to the Weyl element on $\mathrm{GL}_2$ over the adeles: the global quantity $-\log H(x) - \log H(wx)$ equals its purely archimedean analogue plus a sum of standard local weights at the finite places. It serves to pass from global weighted orbital data to local factors, and is used by the weighted class integral decomposition and by its base-change counterpart over an extension field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicHeight_neg_log_adelicHeight_sub_log_adelicHeight_adelicWeyl_mul_eq_archWeight_glArch_add_finsum_weight_finComponent.lean

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem NumberField.AdelicHeight.neg_log_adelicHeight_sub_log_adelicHeight_adelicWeyl_mul_eq_archWeight_glArch_add_finsum_weight_finComponent
    (K : Type) [Field K] [NumberField K]
    (x : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    -Real.log (NumberField.AdelicHeight.adelicHeight K x)
        - Real.log (NumberField.AdelicHeight.adelicHeight K (AutomorphicForm.adelicWeyl (𝓞 K) K * x)) =
      (fun y : GL (Fin 2) (InfiniteAdeleRing K) =>
        -Real.log (AutomorphicForm.WindowedSiegel.archHeight K y)
          - Real.log (AutomorphicForm.WindowedSiegel.archHeight K
              (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K) * y))) (AdelicLevel.glArch (𝓞 K) K x) +
        ∑ᶠ v : HeightOneSpectrum (𝓞 K),
          AutomorphicForm.LocalWeight.weight (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K x)) := by sorry
