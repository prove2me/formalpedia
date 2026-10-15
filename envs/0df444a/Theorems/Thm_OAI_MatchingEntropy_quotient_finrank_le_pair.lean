-- Prove2me | Theorems.Thm_OAI_MatchingEntropy_quotient_finrank_le_pair
-- name    : OAI.MatchingEntropy.quotient_finrank_le_pair
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:11:36.353435+00:00
-- url     : https://prove2.me/theorems/ca243adb-ba5b-4d5f-8a28-2fc1a14c55b9
-- title:
--   Codimension of a subspace containing the joint preimage of two subspaces
-- statement:
--   Let $A$, $B$, $C$ be finite-dimensional real vector spaces with subspaces $U\le A$, $W\le B$ and $Z\le C$, and let $f:A\to B$ and $g:A\to C$ be linear maps such that every $a\in A$ with $f(a)\in W$ and $g(a)\in Z$ belongs to $U$, that is, $f^{-1}(W)\cap g^{-1}(Z)\subseteq U$. Then
--
--   $$
--   \dim(A/U)\;\le\;\dim(B/W)+\dim(C/Z).
--   $$
--
--   The codimension of $U$ is thus bounded by the total codimension of the two subspaces whose joint preimage $U$ contains. In the matching polytope argument, $A$ is the space of directions on the positive support of a point $x$, $U$ is its face space (the directions preserving all constraints active at $x$), and $f,g$ restrict a direction to the two sides of a tight odd cut. The lemma then bounds the face codimension at $x$ by the sum of the face codimensions of the two contracted points.
--
--   **Formalization Note** Dimensions are `Module.finrank ℝ`, and the quotients are the quotient modules `A ⧸ U`, `B ⧸ W`, `C ⧸ Z`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/PerfectMatching/Polyhedron.lean#L98-L113

import Mathlib
import Definitions.Def_MatchingEntropy
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Model
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Basic
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Duality
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Calculus
import Definitions.Def_OAI_Combinatorics_PerfectMatching_SecondVariation
import Definitions.Def_OAI_Combinatorics_PerfectMatching_OddCuts
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Coupling
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Contraction

open OAI OAI.MatchingEntropy
open scoped BigOperators Topology
open Filter
variable {I J : Type*} [Fintype I] [Fintype J]
open Module
variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [Module ℝ A] [Module ℝ B] [Module ℝ C]
  [FiniteDimensional ℝ A] [FiniteDimensional ℝ B] [FiniteDimensional ℝ C]

theorem OAI.MatchingEntropy.quotient_finrank_le_pair (U : Submodule ℝ A) (W : Submodule ℝ B) (Z : Submodule ℝ C)
    (f : A →ₗ[ℝ] B) (g : A →ₗ[ℝ] C)
    (h : ∀ u, f u ∈ W → g u ∈ Z → u ∈ U) :
    finrank ℝ (A ⧸ U) ≤ finrank ℝ (B ⧸ W)+finrank ℝ (C ⧸ Z) := by sorry
