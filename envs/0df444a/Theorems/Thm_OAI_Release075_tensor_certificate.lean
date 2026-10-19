-- Prove2me | Theorems.Thm_OAI_Release075_tensor_certificate
-- name    : OAI.Release075.tensor_certificate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:35:14.08198+00:00
-- url     : https://prove2.me/theorems/21599dbc-4cbd-4375-90dd-988742689e78
-- title:
--   A line certificate turns incidence sums into a block-diagonal identity
-- statement:
--   Let $P$ and $I$ be finite sets, $\mathrm{inc}:P\to\mathcal P(I)$ an incidence, $f:P\times I\to K$ weights in a field, and $(Y_i)_{i\in I}$ matrices of a common shape. Suppose the weights satisfy the certificate
--   $$
--   \sum_{z\in P,\ i\in\mathrm{inc}(z)}f(z,j)f(z,k)=-[j=k=i]\qquad(i,j,k\in I).
--   $$
--   Then, with $W(f_z,Z)$ the matrix $\bigl(f_z(j)f_z(k)Z_{a,b}\bigr)_{(j,a),(k,b)}$,
--   $$
--   \sum_{z\in P}W\Bigl(f_z,\ \sum_{i\in\mathrm{inc}(z)}Y_i\Bigr)=-\operatorname{diag}(Y).
--   $$
--
--   This exchanges the order of summation; it is how the punctured-line certificate enters the rank count.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/MatrixRank.lean#L514-L536

import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank

open OAI OAI.Release075
universe u v
open scoped BigOperators

theorem OAI.Release075.tensor_certificate {P I ι κ K : Type*} [Fintype P] [Fintype I]
    [DecidableEq I] [Field K] (inc : P → Finset I) (f : P → I → K)
    (Y : I → Matrix ι κ K)
    (hline : ∀ i j k, (∑ z, if i ∈ inc z then f z j * f z k else 0) =
      -(if j = i ∧ k = i then 1 else 0)) :
    (∑ z, weightedMatrix (f z) (∑ i ∈ inc z, Y i)) = -diagonalBlocks Y := by sorry
