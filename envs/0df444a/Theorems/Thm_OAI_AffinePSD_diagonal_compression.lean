-- Prove2me | Theorems.Thm_OAI_AffinePSD_diagonal_compression
-- name    : OAI.AffinePSD.diagonal_compression
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T14:11:45.156745+00:00
-- url     : https://prove2.me/theorems/347dd22b-8b88-4982-b458-57d483c1e528
-- title:
--   Compressing a PSD matrix onto the support of a diagonal sum preserves its evaluations
-- statement:
--   Let $I$ and $R$ be finite index sets and $(B_i)_{i\in I}$ a family of real $R\times R$ matrices. The evaluation map is $\mathrm{ev}_B(A)=(\operatorname{tr}(AB_i))_{i\in I}$, and the evaluation cone is $\mathrm{ev}_B(\{A:A\succeq0\})\subseteq\mathbb{R}^I$, the image of the positive semidefinite matrices. Assume every $B_i$ is positive semidefinite and $\sum_iB_i=\operatorname{diag}(d)$ is diagonal.
--
--   For every positive semidefinite $A$ there is a positive semidefinite $A'$ with $\mathrm{ev}_B(A')=\mathrm{ev}_B(A)$ and
--   $$
--   A'_{jj}=0\quad\text{whenever }d_j=0 .
--   $$
--
--   Coordinates where the family vanishes can thus be removed from $A$ without changing any evaluation. This is the first step towards bounding the trace of the matrices realising a bounded point of the cone.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/PSDCompression.lean#L23-L61

import Mathlib
import Definitions.Def_MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PSDEvaluation

open OAI OAI.AffinePSD
open Matrix Finset
open scoped BigOperators
variable {I R : Type*} [Fintype I] [Fintype R] [DecidableEq R]

theorem OAI.AffinePSD.diagonal_compression (B : I → Matrix R R ℝ) (hB : ∀ i, (B i).PosSemidef)
    (d : R → ℝ) (hs : ∑ i, B i = diagonal d) (A : Matrix R R ℝ)
    (hA : A.PosSemidef) :
    ∃ A' : Matrix R R ℝ, A'.PosSemidef ∧ evaluation B A' = evaluation B A ∧
      (∀ j, d j = 0 → A' j j = 0) := by sorry
