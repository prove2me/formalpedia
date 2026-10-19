-- Prove2me | Theorems.Thm_OAI_SeymourSecondNeighborhood_det_blockSupportedVariables_ne_zero
-- name    : OAI.SeymourSecondNeighborhood.det_blockSupportedVariables_ne_zero
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-19T12:19:45.372529+00:00
-- url     : https://prove2.me/theorems/1e96f51c-820d-49ed-acf5-3196a2f0ad7f
-- title:
--   Block-diagonal supported variable matrices with distinct labels per block have nonzero determinant
-- statement:
--   Let $\kappa$ be a finite index set, $R$ an integral domain, and $\beta$ a linearly ordered set of block labels with a block map $\kappa\to\beta$. Let $M$ be the square matrix over $R[X_s]$ with $M_{ij}=X_{\ell(i,j)}$ when $(i,j)$ is in the support, and $0$ otherwise. Assume:
--
--   1. every diagonal position $(i,i)$ is in the support;
--   2. support positions lie within blocks: $(i,j)$ in the support implies $i$ and $j$ are in the same block;
--   3. within a block, distinct support positions carry distinct variables.
--
--   Then
--   $$
--   \det M\ne0 .
--   $$
--
--   Labels may repeat across different blocks. This weakening of the distinct-variable condition is what the coefficient matrices of the pruning argument satisfy.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/GenericRankMatching.lean#L79-L109

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

open OAI OAI.SeymourSecondNeighborhood
open MvPolynomial
variable {R σ m n κ β : Type*}

theorem OAI.SeymourSecondNeighborhood.det_blockSupportedVariables_ne_zero
    [Fintype κ] [DecidableEq κ] [Fintype β] [LinearOrder β]
    [CommRing R] [IsDomain R]
    (support : κ → κ → Prop) (label : κ → κ → σ) (block : κ → β)
    (hdiag : ∀ i, support i i)
    (hblock : ∀ i j, support i j → block i = block j)
    (hlabel : ∀ i j k l, support i j → support k l → block i = block k →
      label i j = label k l → i = k ∧ j = l) :
    (supportedVariableMatrix (R := R) support label).det ≠ 0 := by sorry
