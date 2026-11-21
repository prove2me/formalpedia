-- Prove2me | Theorems.Thm_MasulloGRH_balanced_neighborhood_comparison
-- name    : MasulloGRH.balanced_neighborhood_comparison
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-20T23:58:33.650879+00:00
-- url     : https://prove2.me/theorems/fd6a0ef1-2192-44c5-a394-91b2f9c89d17
-- title:
--   Wengenroth’s comparison of zero neighborhoods on a balanced set
-- statement:
--   Let $E$ be a vector space over a nontrivially normed field, equipped with two topologies $t_1,t_2$ for which scalar multiplication is continuous. Let $A$ be balanced and let $U$ be a $t_1$-neighborhood of zero. Assume that for every $t_1$-neighborhood $V$ of zero there is a $t_2$-neighborhood $W$ of zero with
--   $$W\cap A\cap U\subseteq V.$$
--   Then for every such $V$ there is a $t_2$-neighborhood $W'$ of zero with
--   $$W'\cap A\subseteq V.$$
--   This is the zero-neighborhood comparison used in Wengenroth's Lemma 2.4. Taking $A$ to be a larger step neighborhood permits Proposition 2.5 to preserve local comparison as the step neighborhoods are enlarged.
-- source:
--   Jochen Wengenroth, Acyclic inductive spectra of Fréchet spaces, Studia Mathematica 120 (1996), 247–258, Lemma 2.4 and its use in Proposition 2.5 (p. 251). https://doi.org/10.4064/sm-120-3-247-258 . The formal statement isolates the comparison of relative zero neighborhoods in the proof of Lemma 2.4 and works with balanced sets over a nontrivially normed field.

import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Analysis.SpecificLimits.Normed

open Set Filter
open scoped Pointwise Topology

theorem MasulloGRH.balanced_neighborhood_comparison {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [AddCommGroup E] [Module 𝕜 E] (t₁ t₂ : TopologicalSpace E)
    [@ContinuousSMul 𝕜 E _ _ t₁] [@ContinuousSMul 𝕜 E _ _ t₂]
    {A U : Set E} (hA : Balanced 𝕜 A) (hU : U ∈ @nhds E t₁ 0)
    (hcomp : ∀ V ∈ @nhds E t₁ 0, ∃ W ∈ @nhds E t₂ 0, (W ∩ A) ∩ U ⊆ V) :
    ∀ V ∈ @nhds E t₁ 0, ∃ W ∈ @nhds E t₂ 0, W ∩ A ⊆ V := by sorry
