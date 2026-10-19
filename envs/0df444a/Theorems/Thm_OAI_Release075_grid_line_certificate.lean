-- Prove2me | Theorems.Thm_OAI_Release075_grid_line_certificate
-- name    : OAI.Release075.grid_line_certificate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:36:50.519655+00:00
-- url     : https://prove2.me/theorems/20e7e73f-2fd4-431c-aa07-e43d41304923
-- title:
--   Grid Lagrange weights give an exact punctured-line certificate
-- statement:
--   For a finite field $K$, a finite set $S\subseteq K$ and $a\in S^T$, the grid Lagrange function is $L_a(x)=\prod_{t\in T}\prod_{w\in S\setminus\{a_t\}}\frac{x_t-w}{a_t-w}$ on $K^T$. The punctured line through $a$ with direction $v\ne0$ is $\{a+xv:\ x\in K^{\times}\}$, and $\mathrm{inc}(z)$ is the set of labels $i$ whose punctured line through $a_i$ with direction $v_i$ contains $z$. Assume that the marks $a_i\in S^T$ are pairwise distinct, every $v_i\ne0$, and
--   $$
--   2\,|T|\,(|S|-1)<|K|-1 .
--   $$
--   Then for all labels $i,j,k$,
--   $$
--   \sum_{z:\ i\in\mathrm{inc}(z)}L_{a_j}(z)\,L_{a_k}(z)=-[j=k=i].
--   $$
--
--   This is the certificate fed into the rank argument.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/MatrixRank.lean#L726-L751

import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank

open OAI OAI.Release075
universe u v
open scoped BigOperators

theorem OAI.Release075.grid_line_certificate {T I K : Type*} [Fintype T] [Fintype I]
    [DecidableEq T] [DecidableEq I] [Field K] [Fintype K] [DecidableEq K]
    (S : Finset K) (a v : I → T → K) (ha : ∀ i t, a i t ∈ S)
    (hinj : Function.Injective a) (hv : ∀ i, v i ≠ 0)
    (hdeg : 2 * (Fintype.card T * (S.card - 1)) < Fintype.card K - 1) :
    ∀ i j k, (∑ z, if i ∈ lineIncidence a v z then
      gridLagrange S (a j) z * gridLagrange S (a k) z else 0) =
      -(if j = i ∧ k = i then 1 else 0) := by sorry
