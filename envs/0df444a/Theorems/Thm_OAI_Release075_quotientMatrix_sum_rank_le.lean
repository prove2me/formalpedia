-- Prove2me | Theorems.Thm_OAI_Release075_quotientMatrix_sum_rank_le
-- name    : OAI.Release075.quotientMatrix_sum_rank_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:35:46.370568+00:00
-- url     : https://prove2.me/theorems/0c207ab8-faa0-449d-b8a5-a7f8e037c533
-- title:
--   A Cartesian block contributes rank at most the group order
-- statement:
--   For a finite group $F$, write $\rho(x)$ for the $F\times F$ permutation matrix of left multiplication, $\rho(x)_{a,b}=[a=xb]$. For $g:\iota\times\iota\to F$ the quotient matrix $Y(g)$ is the $(\iota\times F)\times(\iota\times F)$ block matrix with blocks $\rho(g(u,v))$. The family $g$ has surviving rectangles if $g(u,v)g(u',v)^{-1}g(u',v')g(u,v')^{-1}\ne1$ whenever $u\ne u'$ and $v\ne v'$. Let $s,t$ be finite sets, $L:\iota\times s\to F$ and $R:\iota\times t\to F$. Then over any field
--   $$
--   \operatorname{rank}\sum_{j\in s}\sum_{k\in t}Y\bigl((u,v)\mapsto L(u,j)^{-1}R(v,k)\bigr)\le|F| .
--   $$
--
--   So a local Cartesian block factors through a single copy of the regular module.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/MatrixRank.lean#L552-L577

import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank

open OAI OAI.Release075
universe u v
open scoped BigOperators

theorem OAI.Release075.quotientMatrix_sum_rank_le {ι s t F K : Type*} [Fintype ι]
    [Fintype s] [Fintype t] [Group F] [Fintype F] [DecidableEq F] [Field K]
    (L : ι → s → F) (R : ι → t → F) :
    (∑ j : s, ∑ k : t, quotientMatrix (R := K) (fun u v => (L u j)⁻¹ * R v k)).rank ≤
      Fintype.card F := by sorry
