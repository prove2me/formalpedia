-- Prove2me | Theorems.Thm_OAI_RecursivePotentials_IsReflexive_of_equiv
-- name    : OAI.RecursivePotentials.IsReflexive.of_equiv
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T08:17:56.072098+00:00
-- url     : https://prove2.me/theorems/9df664b6-e81a-4cb1-908a-acb31f7db17b
-- title:
--   Reflexivity is preserved by continuous linear isomorphisms
-- statement:
--   For a real normed space $E$, write $E^{*}$ for the space of continuous linear functionals on $E$ and $J_E:E\to E^{**}$ for the canonical map $J_E(x)(f)=f(x)$. The space $E$ is *reflexive* if $J_E$ is surjective (no completeness is assumed in this definition).
--
--   **Theorem.** Let $E$ and $F$ be real normed spaces, and let $e:E\to F$ be a continuous linear equivalence (a linear bijection such that $e$ and $e^{-1}$ are continuous). If $E$ is reflexive, then so is $F$:
--
--   $$J_E(E)=E^{**}\ \Longrightarrow\ J_F(F)=F^{**}.$$
--
--   Reflexivity is thus an isomorphic (not merely isometric) invariant. In the development it transfers reflexivity from Hilbert and $\ell^2$-sum models to tree spaces that are only isomorphic to them.
--
--   **Formalization Note** Reflexivity is the predicate `IsReflexive E`, the surjectivity of `NormedSpace.inclusionInDoubleDual ℝ E`; the equivalence is `e : E ≃L[ℝ] F`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/RecursivePotentials/JoinedGeometry.lean#L182-L198

import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model
import Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_ZeroRootGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_EquivalentNorms
import Definitions.Def_OAI_Analysis_RecursivePotentials_JoinedGeometry

open OAI OAI.RecursivePotentials
universe uIndex uSpace uOther uDomain uTarget uFiber
open scoped BigOperators
open Filter Topology
open Filter Topology
open scoped ENNReal

theorem OAI.RecursivePotentials.IsReflexive.of_equiv {E : Type uSpace} {F : Type uOther} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (hE : IsReflexive E) (e : E ≃L[ℝ] F) :
    IsReflexive F := by sorry
