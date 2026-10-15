-- Prove2me | Theorems.Thm_OAI_CompactBanach_exists_auerbach_basis
-- name    : OAI.CompactBanach.exists_auerbach_basis
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T07:04:41.729454+00:00
-- url     : https://prove2.me/theorems/71229204-8213-4a18-bdaf-78d89f9df595
-- title:
--   Auerbach's lemma: a basis of vectors of norm at most one whose coordinate functionals have norm at most one
-- statement:
--   Let $E$ be a finite-dimensional real normed space and let $\iota$ be a finite index set such that $E$ has some basis $(e_i)_{i\in\iota}$ indexed by $\iota$. Then $E$ has a basis $(b_i)_{i\in\iota}$, indexed by the same set, such that, writing $b_i^*:E\to\mathbb{R}$ for the $i$-th coordinate functional of this basis (so that $x=\sum_{i\in\iota} b_i^*(x)\,b_i$ for every $x\in E$),
--   $$
--   \|b_i\|\le1\qquad\text{and}\qquad |b_i^*(x)|\le\|x\|\qquad\text{for all } i\in\iota \text{ and all } x\in E .
--   $$
--
--   Since $b_i^*(b_i)=1$, the second inequality forces $\|b_i\|\ge1$; hence every $b_i$ is a unit vector and every coordinate functional has operator norm exactly $1$, which is the classical form of Auerbach's lemma. The lemma provides, in any finite-dimensional normed space, a basis in which each single coefficient of a vector is controlled by the norm of the vector, as for an orthonormal basis; it is used to build finite systems of vectors in arbitrary infinite-dimensional normed spaces with the same property.
--
--   **Formalization Note** The bases are `Module.Basis ι ℝ E` and $b_i^*(x)$ is `b.repr x i`. The given basis `e` only serves to fix the index type, which carries `Fintype` and `DecidableEq` instances.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/Auerbach.lean#L10-L67

import Mathlib
import Definitions.Def_CompactBanach
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives
import Definitions.Def_OAI_Geometry_DoublingHilbert_Integration
import Definitions.Def_OAI_Geometry_DoublingHilbert_Rectangles
import Definitions.Def_OAI_Geometry_DoublingHilbert_Grids
import Definitions.Def_OAI_Geometry_DoublingHilbert_SelectedSheets
import Definitions.Def_OAI_Geometry_DoublingHilbert_Energy
import Definitions.Def_OAI_Geometry_DoublingHilbert_Crossings
import Definitions.Def_OAI_Geometry_DoublingHilbert_Doubling

open OAI OAI.CompactBanach
open Set Metric
open scoped BigOperators

theorem OAI.CompactBanach.exists_auerbach_basis {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : Module.Basis ι ℝ E) :
    ∃ b : Module.Basis ι ℝ E, (∀ i, ‖b i‖ ≤ 1) ∧
      ∀ x i, |b.repr x i| ≤ ‖x‖ := by sorry
