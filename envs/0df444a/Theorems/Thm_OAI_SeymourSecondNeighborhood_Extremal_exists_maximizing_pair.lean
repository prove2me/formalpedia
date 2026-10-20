-- Prove2me | Theorems.Thm_OAI_SeymourSecondNeighborhood_Extremal_exists_maximizing_pair
-- name    : OAI.SeymourSecondNeighborhood.Extremal.exists_maximizing_pair
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T12:39:23.458262+00:00
-- url     : https://prove2.me/theorems/ff1ec31e-4762-4e3a-b87a-dbe016653816
-- title:
--   Some admissible pair maximizes the counting objective
-- statement:
--   Let $r$ be a relation on a finite set $V$. For $P,Q\subseteq V\times V$ let $u(P,Q)$ be the number of pairs lying neither in the left image $\{z:\exists p,\ (p,z_2)\in P,\ p\to z_1\}$ nor in the right image $\{z:\exists s,\ (z_1,s)\in Q,\ s\to z_2\}$. Put $\Omega(P,Q)=|P|+|Q|+u(P,Q)$.
--
--   Let $\mathcal{A}$ be any predicate on pairs $(P,Q)$ that holds for at least one pair. Then there is $(P,Q)$ satisfying $\mathcal{A}$ such that
--   $$
--   \Omega(P',Q')\le\Omega(P,Q)\quad\text{for all }(P',Q')\text{ satisfying }\mathcal{A}.
--   $$
--
--   The final contradiction is applied to such a maximizer among admissible pairs. A pruning step would produce an admissible pair with strictly larger objective.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/ExtremalCounting.lean#L53-L68

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
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_AugmentedGraph
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MatchingAugmented
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_GenericRankMatching
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_GenericRank
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MatrixMaps
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_KernelRestriction
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MaxSupportKernel
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_KernelConflict
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_GenericRankCoefficients
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MatrixMapsPolynomial
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_GenericRankGlobalMinors
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_KernelBasisLifts
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_ExtremalImages
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_ExtremalCompatibility
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_ExtremalCounting

open OAI OAI.SeymourSecondNeighborhood OAI.SeymourSecondNeighborhood.Extremal
open Pruning
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem OAI.SeymourSecondNeighborhood.Extremal.exists_maximizing_pair (r : V → V → Prop)
    (admissible : Finset (V × V) → Finset (V × V) → Prop)
    (hex : ∃ P Q, admissible P Q) :
    ∃ P Q, admissible P Q ∧ ∀ P' Q', admissible P' Q' →
      objective r P' Q' ≤ objective r P Q := by sorry
