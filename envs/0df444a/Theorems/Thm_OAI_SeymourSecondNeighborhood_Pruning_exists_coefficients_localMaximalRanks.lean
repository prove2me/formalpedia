-- Prove2me | Theorems.Thm_OAI_SeymourSecondNeighborhood_Pruning_exists_coefficients_localMaximalRanks
-- name    : OAI.SeymourSecondNeighborhood.Pruning.exists_coefficients_localMaximalRanks
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T12:30:30.0132+00:00
-- url     : https://prove2.me/theorems/de7d1623-66aa-4f62-89cf-36b289cacadb
-- title:
--   Generic coefficients with locally maximal ranks avoiding finitely many polynomials
-- statement:
--   Let $r$ be a relation on a finite set $X$ and $R,C\subseteq X\times X$. The coefficient variables are two copies of $X\times X$. For a real assignment $v$ of the variables, the selected coefficients $a_v(x,y)$ and $b_v(x,y)$ equal the value of the corresponding variable of the first, respectively second, copy when $x\to y$, and $0$ otherwise. The coefficients $b$ have locally maximal ranks if for every arc $p\to i$, the local matrix $D^{(p,i)}_b=(b(s,j))_{s\in C_i,\,j\in R_p}$, with $C_i=\{s:(i,s)\in C\}$ and $R_p=\{j:(p,j)\in R\}$, has the largest rank among all real matrices on $C_i\times R_p$ vanishing outside the positions $(s,j)$ with $s\to j$.
--
--   Let $(f_t)_{t\in\tau}$ be a finite family of nonzero real polynomials in the coefficient variables. Then there is an assignment $v$ such that
--   $$
--   f_t(v)\ne0\quad\text{for all }t\in\tau,
--   $$
--   $a_v$ and $b_v$ are supported on arcs, and $b_v$ has locally maximal ranks.
--
--   The extra polynomials will be the determinants of matching minors. One generic choice of coefficients thus gives locally maximal ranks and nonsingular matching minors at the same time.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/GenericRankCoefficients.lean#L48-L73

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

open OAI OAI.SeymourSecondNeighborhood OAI.SeymourSecondNeighborhood.Pruning
variable {X τ : Type*} [Fintype X] [DecidableEq X] [Fintype τ]

theorem OAI.SeymourSecondNeighborhood.Pruning.exists_coefficients_localMaximalRanks
    (r : X → X → Prop) (R C : Finset (X × X))
    (extra : τ → MvPolynomial (CoefficientVariables X) ℝ)
    (hextra : ∀ t, extra t ≠ 0) :
    ∃ v : CoefficientVariables X → ℝ,
      (∀ t, MvPolynomial.eval v (extra t) ≠ 0) ∧
      SupportedCoefficients r (selectedA r v) ∧
      SupportedCoefficients r (selectedB r v) ∧
      LocalMaximalRanks r R C (selectedB r v) := by sorry
