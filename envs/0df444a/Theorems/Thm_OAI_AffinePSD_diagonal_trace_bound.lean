-- Prove2me | Theorems.Thm_OAI_AffinePSD_diagonal_trace_bound
-- name    : OAI.AffinePSD.diagonal_trace_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T14:13:14.066018+00:00
-- url     : https://prove2.me/theorems/467c9823-97dc-47f9-89ca-7caf626dfe70
-- title:
--   A trace bound for PSD matrices supported where the diagonal sum is positive
-- statement:
--   Let $I$ and $R$ be finite index sets and $(B_i)_{i\in I}$ a family of real $R\times R$ matrices. The evaluation map is $\mathrm{ev}_B(A)=(\operatorname{tr}(AB_i))_{i\in I}$, and the evaluation cone is $\mathrm{ev}_B(\{A:A\succeq0\})\subseteq\mathbb{R}^I$, the image of the positive semidefinite matrices. Assume every $B_i$ is positive semidefinite and $\sum_iB_i=\operatorname{diag}(d)$ is diagonal. Let $A$ be positive semidefinite with $A_{jj}=0$ whenever $d_j=0$. Then
--   $$
--   \operatorname{tr}A\le\Bigl(\sum_{j\in R}d_j^{-1}\Bigr)\sum_{i\in I}\operatorname{tr}(AB_i),
--   $$
--   with the convention $0^{-1}=0$.
--
--   So the trace of a compressed matrix is controlled by the sum of its evaluations. Points of the cone in a bounded set are therefore realised by matrices of bounded trace.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/PSDCompression.lean#L80-L98

import Mathlib
import Definitions.Def_MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PSDEvaluation

open OAI OAI.AffinePSD
open Matrix Finset
open scoped BigOperators
variable {I R : Type*} [Fintype I] [Fintype R] [DecidableEq R]

theorem OAI.AffinePSD.diagonal_trace_bound (B : I → Matrix R R ℝ) (hB : ∀ i, (B i).PosSemidef)
    (d : R → ℝ) (hs : ∑ i, B i = diagonal d) (A : Matrix R R ℝ)
    (hA : A.PosSemidef) (hz : ∀ j, d j = 0 → A j j = 0) :
    A.trace ≤ (∑ j, (d j)⁻¹) * ∑ i, evaluation B A i := by sorry
