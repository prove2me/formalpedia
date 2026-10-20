-- Prove2me | Theorems.Thm_OAI_SeymourSecondNeighborhood_blowup_isOriented
-- name    : OAI.SeymourSecondNeighborhood.blowup_isOriented
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T12:07:06.578637+00:00
-- url     : https://prove2.me/theorems/e03319e7-11df-4d41-a8e2-6b32c03fc02f
-- title:
--   The transitive blow-up of an oriented graph is oriented
-- statement:
--   Let $r$ be an oriented relation on $V$ (no loops, no 2-cycles) and $m\in\mathbb{N}$. Then the blow-up on $V\times\{0,\dots,m-1\}$,
--   $$
--   (x,i)\to(y,j)\iff r(x,y)\ \text{or}\ (x=y\ \text{and}\ i<j),
--   $$
--   is again oriented.
--
--   Blow-ups stay inside the class of oriented graphs, so the second neighbourhood question makes sense for them.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/TransitiveBlowup.lean#L13-L29

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

open OAI OAI.SeymourSecondNeighborhood
variable {V : Type*}

theorem OAI.SeymourSecondNeighborhood.blowup_isOriented {r : V → V → Prop} (hr : IsOriented r) (m : ℕ) :
    IsOriented (blowup r m) := by sorry
