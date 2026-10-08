-- Prove2me | Theorems.Thm_HartSchmeidler_Compact_exists_uniform_partition
-- name    : HartSchmeidler.Compact.exists_uniform_partition
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T12:14:28.091119+00:00
-- url     : https://prove2.me/theorems/a579ad21-fcaa-4863-b5ba-71acff2b5781
-- title:
--   Proof of Theorem 3, p. 25 — a finite Borel partition of Sⁱ on whose pieces hⁱ varies by less than ε
-- statement:
--   Let each $S^i$ be a nonempty compact Hausdorff space with its Borel σ-algebra, let $S=\prod_jS^j$ carry the product topology, and let $h^i:S\to\mathbb R$ be continuous. Fix a player $i$ and $\varepsilon>0$. Then there is a finite partition of $S^i$ into pairwise disjoint nonempty Borel sets $A_1,\dots,A_K$ such that
--   $$
--   \bigl|h^i(s^{-i},a)-h^i(s^{-i},b)\bigr|<\varepsilon\qquad\text{whenever } a,b\in A_k \text{ for some } k,\ \text{for every } s^{-i}\in S^{-i}.
--   $$
--
--   The partition discretizes player $i$'s strategy space uniformly in the opponents' profile; it is the device that reduces a general measurable deviation to finitely many deviations of the special form.
--
--   **Formalization Note** The pieces are required to be nonempty, because the proof next fixes a point $t_k^i\in A_k$; empty pieces of a partition can be discarded, so this costs nothing. $(s^{-i},a)$ is the profile $s$ with its $i$-th coordinate replaced by $a$, and the bound is required for every profile $s$. If $S^i$ were empty the partition would have $K=0$ pieces, but $S^i$ is nonempty here.
-- source:
--   Hart and Schmeidler, Existence of Correlated Equilibria, Math. Oper. Res. 14 (1989), p. 25, proof of Theorem 3, "The general case" ("it is straightforward to obtain a finite partition of S^i"); https://doi.org/10.1287/moor.14.1.18

import Definitions.Def_HartSchmeidler_Compact_Game

namespace HartSchmeidler.Compact

open MeasureTheory

/-- Proof of Theorem 3, p. 25, the general case: for continuous `hⁱ` on the compact `S` and
`ε > 0`, `Sⁱ` has a finite partition into nonempty Borel sets `A₁, …, A_K` such that
`|hⁱ(s⁻ⁱ, a) − hⁱ(s⁻ⁱ, b)| < ε` whenever `a, b` lie in the same `A_k`, for every `s⁻ⁱ`. -/
theorem exists_uniform_partition {ι : Type*} [Nonempty ι] [DecidableEq ι] {S : ι → Type*}
    [∀ i, TopologicalSpace (S i)] [∀ i, CompactSpace (S i)] [∀ i, T2Space (S i)]
    [∀ i, Nonempty (S i)] [∀ i, MeasurableSpace (S i)] [∀ i, BorelSpace (S i)]
    (h : ι → Profile S → ℝ) (hcont : ∀ i, Continuous (h i))
    (i : ι) (ε : ℝ) (hε : 0 < ε) :
    ∃ (K : ℕ) (A : Fin K → Set (S i)),
      (∀ k, MeasurableSet (A k)) ∧ (∀ k, (A k).Nonempty) ∧ Pairwise (Function.onFun Disjoint A) ∧
        (⋃ k, A k) = Set.univ ∧
        ∀ k, ∀ a ∈ A k, ∀ b ∈ A k, ∀ s : Profile S,
          |h i (Function.update s i a) - h i (Function.update s i b)| < ε := by sorry

end HartSchmeidler.Compact
