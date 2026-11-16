-- Prove2me | Theorems.Thm_MSTCuts2027_Parallel_Supplement_equal_cross_mincut_values
-- name    : MSTCuts2027.Parallel.Supplement.equal_cross_mincut_values
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:40:20.158688+00:00
-- url     : https://prove2.me/theorems/228272bd-e19f-4779-ae71-3f03cc50b987
-- title:
--   Lemma 11 — equal mincut values across two vertex sets
-- statement:
--   Let $F$ be a symmetric real cut function on a finite vertex set $V$, and let $V_1,V_2\subseteq V$ be disjoint. Suppose that the mincut value of every pair of distinct vertices of $V_1$, and of every pair of distinct vertices of $V_2$, is at least the mincut value of every pair in $V_1\times V_2$:
--   $$\lambda_1(x,y)\le\lambda_1(a,b)\qquad\text{for all } x\in V_1,\ y\in V_2 \text{ and distinct } a,b \text{ both in } V_1 \text{ or both in } V_2.$$
--   Then all pairs of $V_1\times V_2$ have the same mincut value: $\lambda_1(x,y)=\lambda_1(x',y')$ for all $x,x'\in V_1$ and $y,y'\in V_2$.
--
--   This is the structural fact that lets the all-pairs second-mincut algorithm merge two trees along every cross edge at once (Theorem 5, clause 3).
--
--   Differences from the source:
--   - encoding: pairs in V1 × V1 and V2 × V2 → pairs of distinct vertices; reason: λ1 is defined only on pairs of distinct vertices
--   - generalization: standing assumption that every pair has a second mincut → not assumed; reason: the lemma is about mincut values only; the source statement is the special case with the assumption
-- source:
--   Baswana–Roy, Using MSTs to Compute All-Pairs Mincuts and Beyond ..., STOC 2027 submission #21, pinned preprint SHA-256 faa337be0f0f1bfbbcf924cb3591bd51ded2a6ef2c9e2154e00534a840156a11, Lemma 11, printed p. 14, PDF p. 16

import Mathlib
import Definitions.Def_FlowsNetworks_MultiTerminal_SpanningSubtree
import Definitions.Def_MSTCuts2027_Parallel_CutModel
import Definitions.Def_MSTCuts2027_Parallel_Supplement_SecondCutModel

namespace MSTCuts2027.Parallel.Supplement

open MSTCuts2027.Parallel

/-- Lemma 11: if no pair inside `V₁` or inside `V₂` has a smaller mincut value than a pair of
`V₁ × V₂`, then all pairs of `V₁ × V₂` have the same mincut value. -/
theorem equal_cross_mincut_values {V : Type} [Fintype V] [DecidableEq V]
    (F : Finset V → ℝ) (hF : IsSymmetricCutFunction F)
    (V₁ V₂ : Finset V) (hdisj : Disjoint V₁ V₂)
    (h₁ : ∀ a ∈ V₁, ∀ b ∈ V₁, a ≠ b → ∀ x ∈ V₁, ∀ y ∈ V₂, lam F x y ≤ lam F a b)
    (h₂ : ∀ a ∈ V₂, ∀ b ∈ V₂, a ≠ b → ∀ x ∈ V₁, ∀ y ∈ V₂, lam F x y ≤ lam F a b) :
    ∀ x ∈ V₁, ∀ x' ∈ V₁, ∀ y ∈ V₂, ∀ y' ∈ V₂, lam F x y = lam F x' y' := by sorry

end MSTCuts2027.Parallel.Supplement
