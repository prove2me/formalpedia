-- Prove2me | Theorems.Thm_OAI_SeymourSecondNeighborhood_Bipartite_matching_card_le_cover_card
-- name    : OAI.SeymourSecondNeighborhood.Bipartite.matching_card_le_cover_card
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T12:10:50.025768+00:00
-- url     : https://prove2.me/theorems/e91e8b37-5f16-4e8f-9214-008a60394f9e
-- title:
--   A matching is no larger than a vertex cover
-- statement:
--   Let $E\subseteq L\times R$ be a bipartite relation, $M$ a matching (edges of $E$ pairwise disjoint in both endpoints) and $(A,B)$ a vertex cover ($A\subseteq L$, $B\subseteq R$, every edge has its left end in $A$ or its right end in $B$). Then
--   $$
--   |M|\le|A|+|B| .
--   $$
--
--   This is the easy half of König's theorem. Exhibiting a matching therefore gives a lower bound on every cover, which is how deletions are counted in the pruning lemma.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/Matching.lean#L89-L113

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.Tauto
import Definitions.Def_SeymourSecondNeighborhood
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Basic
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_ReductionCore
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Reindex
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MinimalCounterexample
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Deletion
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_TransitiveBlowup
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_PruningDefinitions
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Matching

open OAI OAI.SeymourSecondNeighborhood OAI.SeymourSecondNeighborhood.Bipartite
variable {L R : Type*}
variable [DecidableEq L] [DecidableEq R]

omit [DecidableEq R] in
theorem OAI.SeymourSecondNeighborhood.Bipartite.matching_card_le_cover_card {E : L → R → Prop}
    {M : Finset (L × R)} {A : Finset L} {B : Finset R}
    (hM : IsMatching E M) (hC : IsVertexCover E A B) :
    M.card ≤ A.card + B.card := by sorry
