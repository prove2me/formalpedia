-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Curvature_determinant_tuning
-- name    : OAI.AsymptoticallyMinimalLittlewood.Curvature.determinant_tuning
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:56:31.984668+00:00
-- url     : https://prove2.me/theorems/5df63181-379c-413b-aec7-1c6eb94b72f3
-- title:
--   Tuning products of values of non-parallel linear forms: $\prod_j|f_i(b_j)|$ within a factor $1\pm\delta$ of $\tau A_i$ for all $i$
-- statement:
--   Let $I$ be a finite index set and $V$ a finite-dimensional real normed vector space. Let $(f_i)_{i\in I}$ be linear functionals $f_i:V\to\mathbb{R}$ such that $f_i\ne 0$ for every $i$, and such that for $i\ne j$ the functional $f_i$ is not a scalar multiple of $f_j$ (that is, $f_i\ne c\,f_j$ for every $c\in\mathbb{R}$). Let $A_i>0$ for $i\in I$, and let $0<\delta<1$. Then there exist $\tau>0$ and vectors $(b_j)_{j\in I}$ in $V$ such that $f_i(b_j)\ne 0$ for all $i,j\in I$ and, for every $i\in I$,
--
--   $$
--   (1-\delta)\,\tau A_i\le\prod_{j\in I}\bigl|f_i(b_j)\bigr|\le(1+\delta)\,\tau A_i .
--   $$
--
--   In words: one family of vectors, indexed by the same set as the functionals, can be chosen so that the $|I|$ products $\prod_j|f_i(b_j)|$ are simultaneously proportional, up to relative error $\delta$ and a common factor $\tau$, to arbitrarily prescribed positive weights $A_i$, with no factor $f_i(b_j)$ vanishing. In the construction of flat Littlewood polynomials these products play the role of products of curvatures, and the weights $A_i$ are built from prescribed squared Fourier coefficients.
--
--   **Formalization Note** The functionals are `V →ₗ[ℝ] ℝ`. The norm on $V$ only serves to give $V$ its usual topology, in which linear functionals are continuous; any finite-dimensional real vector space can be used.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Curvature.lean#L54-L121

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket

open OAI OAI.AsymptoticallyMinimalLittlewood
universe uV uI
open scoped BigOperators Topology
open Filter

theorem OAI.AsymptoticallyMinimalLittlewood.Curvature.determinant_tuning {I : Type uI} {V : Type uV} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (f : I → V →ₗ[ℝ] ℝ) (hf : ∀ i, f i ≠ 0)
    (hpair : ∀ i j, i ≠ j → ∀ c : ℝ, f i ≠ c • f j)
    (A : I → ℝ) (hA : ∀ i, 0 < A i) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ τ : ℝ, 0 < τ ∧ ∃ b : I → V,
      (∀ i j, f i (b j) ≠ 0) ∧
      ∀ i, (1-δ)*τ*A i ≤ ∏ j, |f i (b j)| ∧
        (∏ j, |f i (b j)|) ≤ (1+δ)*τ*A i := by sorry
