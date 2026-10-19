-- Prove2me | Theorems.Thm_OAI_SeymourSecondNeighborhood_Bipartite_exists_maximum_matching_min_cost
-- name    : OAI.SeymourSecondNeighborhood.Bipartite.exists_maximum_matching_min_cost
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-19T12:11:16.184811+00:00
-- url     : https://prove2.me/theorems/9067dec2-7191-465b-b5ce-fb32c9cacf2f
-- title:
--   A maximum matching of minimal cost exists
-- statement:
--   Let $L,R$ be finite, $E\subseteq L\times R$, and $\mathrm{cost}$ any function from finite edge sets to $\mathbb{N}$. Then there is a maximum matching $M$ such that every matching $N$ with $|N|=|M|$ satisfies
--   $$
--   \mathrm{cost}(M)\le\mathrm{cost}(N).
--   $$
--
--   Among all maximum matchings one can fix an extremal one for a secondary objective. Such a doubly extremal matching is used to derive structural information in the pruning argument.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/Matching.lean#L133-L151

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
variable [Fintype L] [Fintype R]

theorem OAI.SeymourSecondNeighborhood.Bipartite.exists_maximum_matching_min_cost (E : L → R → Prop)
    (cost : Finset (L × R) → ℕ) :
    ∃ M, IsMaximumMatching E M ∧
      ∀ N, IsMatching E N → N.card = M.card → cost M ≤ cost N := by sorry
