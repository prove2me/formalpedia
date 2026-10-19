-- Prove2me | Theorems.Thm_OAI_Release075_exists_alteration_budget
-- name    : OAI.Release075.exists_alteration_budget
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:45:57.734925+00:00
-- url     : https://prove2.me/theorems/510b06dd-9b46-4589-a64b-ce1fa6f6511f
-- title:
--   Some direction assignment meets the strict rank budget
-- statement:
--   Let $S$ be a finite set of marks in a finite vector space $V$ over a finite field $K$, and let $\omega:S\to\mathbb P(V)$ be a uniformly random direction assignment. A mark is deleted if it lies on an occurring cycle candidate of length $2,\dots,6$ (a cyclic sequence of distinct points whose consecutive pairs are joined by the lines of distinct marks); the others are retained. The degree of a point $z$ counts marks whose line passes through $z\ne$ mark, with mean $\mu(z)=\sum_{a\in S}[z\ne a]/|\mathbb P(V)|$. The exceptional points for a threshold $T$ are the points of degree $<T$ together with all points on lines of deleted marks. Let $\mu>0$ with $2T\le\mu\le\mu(z)$ for all $z$, and let $B$ bound the expected number of deleted marks. If
--   $$
--   8|V|+\frac{16r|V|}{\mu}+r\bigl(4|K|+1\bigr)B<|S|\,r ,
--   $$
--   then some assignment $\omega$ satisfies
--   $$
--   4\bigl(2|V|+r\,|E_\omega|\bigr)<|\text{retained marks}|\cdot r ,
--   $$
--   where $E_\omega$ is the set of exceptional points.
--
--   This is the single averaging step that fixes the directions once and for all.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/Incidence.lean#L683-L724

import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence

open OAI OAI.Release075
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype K] [Fintype V] [Nontrivial V] [Fintype (Projectivization K V)]

theorem OAI.Release075.exists_alteration_budget (S : Finset V) (r T : ℕ) (μ B : ℝ)
    (hμ : 0 < μ) (hT : 2 * (T : ℝ) ≤ μ)
    (hlower : ∀ z : V, μ ≤ pointMean (K := K) S z)
    (hdel : (𝔼 ω : S → Projectivization K V, ((deletedMarks S ω).card : ℝ)) ≤ B)
    (hbudget : 8 * (Fintype.card V : ℝ) + 16*r*(Fintype.card V : ℝ)/μ +
        r*(4*(Fintype.card K : ℝ)+1)*B < (S.card : ℝ)*r) :
    ∃ ω : S → Projectivization K V,
      4 * (2 * Fintype.card V + r * (exceptionalPoints S ω T).card) <
        Fintype.card (Retained S ω) * r := by sorry
