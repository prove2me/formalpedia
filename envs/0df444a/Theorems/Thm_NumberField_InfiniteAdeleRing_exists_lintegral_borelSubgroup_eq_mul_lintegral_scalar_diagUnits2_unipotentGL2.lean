-- Prove2me | Theorems.Thm_NumberField_InfiniteAdeleRing_exists_lintegral_borelSubgroup_eq_mul_lintegral_scalar_diagUnits2_unipotentGL2
-- name    : NumberField.InfiniteAdeleRing.exists_lintegral_borelSubgroup_eq_mul_lintegral_scalar_diagUnits2_unipotentGL2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/d5cb7b0d-a3e9-54ce-9b4e-21bc7e001ede
-- title:
--   Archimedean Borel Haar measure in z(u)a(t)n(x) coordinates
-- statement:
--   Let $K$ be a number field and let $K_\infty$ denote its infinite adele ring, equipped with a measurable structure which is the Borel structure of its topology, and similarly for the topological group $K_\infty^\times$ of units. Let $\lambda$ be an additive Haar measure on $K_\infty$, let $\rho$ be a Haar measure on $K_\infty^\times$, and let $\mu_B$ be a Haar measure on the subgroup [`AutomorphicForm.borelSubgroup`](def/AutomorphicForm_BorelSubgroup.html#L12) of $GL_2(K_\infty)$ consisting of those invertible matrices whose $(1,0)$ entry vanishes (the upper-triangular subgroup $B$), taken with respect to the Borel $\sigma$-algebra induced on it. The assertion is that there exists a constant $c \in [0,\infty]$ with $c \neq 0$ and $c \neq \infty$, independent of the integrand, such that for every function $F : GL_2(K_\infty) \to [0,\infty]$ measurable for the Borel $\sigma$-algebra [`AutomorphicForm.glBorelOf`](def/AutomorphicForm_TwistedOrbital.html#L57) on $GL_2(K_\infty)$ one has $$\int_B F(b)\,d\mu_B(b) \;=\; c \int_{K_\infty^\times}\!\int_{K_\infty^\times}\!\int_{K_\infty} F\bigl(\mathrm{diag}(u,u)\cdot \mathrm{diag}(t,1)\cdot \begin{pmatrix}1&x\\0&1\end{pmatrix}\bigr)\,d\lambda(x)\,d\rho(t)\,d\rho(u),$$ all integrals being lower Lebesgue integrals of $[0,\infty]$-valued functions; here $\mathrm{diag}(u,u)$ is the scalar element attached to the unit $u$, $\mathrm{diag}(t,1)$ is `diagUnits2 t 1`, and the last factor is [`AutomorphicForm.unipotentGL2 x`](def/AutomorphicForm_ConstantTerm.html#L17). In particular no modular factor in $t$ occurs in this ordering of the coordinates.
--
--   This is the archimedean Iwasawa-type decomposition of a Haar measure on the upper-triangular subgroup $B = T \ltimes N$ of $GL_2(K_\infty)$, written in the order centre, torus, unipotent, for which the product measure is already left invariant. It feeds the corresponding coordinate formula for an integral over $GL_2(K_\infty)$ obtained by combining $B$ with the row-isometry coordinates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_InfiniteAdeleRing_exists_lintegral_borelSubgroup_eq_mul_lintegral_scalar_diagUnits2_unipotentGL2.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BorelSubgroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped ENNReal

attribute [local instance] AutomorphicForm.centralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

theorem NumberField.InfiniteAdeleRing.exists_lintegral_borelSubgroup_eq_mul_lintegral_scalar_diagUnits2_unipotentGL2
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]
    (lam : Measure (InfiniteAdeleRing K)) [lam.IsAddHaarMeasure]
    [MeasurableSpace (InfiniteAdeleRing K)ˣ] [BorelSpace (InfiniteAdeleRing K)ˣ]
    (ρ : Measure (InfiniteAdeleRing K)ˣ) [ρ.IsHaarMeasure]
    (μB : @Measure ↥(AutomorphicForm.borelSubgroup (InfiniteAdeleRing K)) (borel _))
    (hμB : @Measure.IsHaarMeasure _ _ _ (borel _) μB) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
      ∀ F : GL (Fin 2) (InfiniteAdeleRing K) → ℝ≥0∞, Measurable[AutomorphicForm.glBorelOf (InfiniteAdeleRing K)] F →
        @lintegral _ (borel _) μB (fun b => F (b : GL (Fin 2) (InfiniteAdeleRing K))) =
          c * ∫⁻ u, ∫⁻ t, ∫⁻ x,
                F (Matrix.GeneralLinearGroup.scalar (Fin 2) u * diagUnits2 t 1 * AutomorphicForm.unipotentGL2 x)
              ∂lam ∂ρ ∂ρ := by sorry
