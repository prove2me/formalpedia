-- Prove2me | Theorems.Thm_OAI_Release075_finite_quotient_rank_obstruction
-- name    : OAI.Release075.finite_quotient_rank_obstruction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:37:20.600691+00:00
-- url     : https://prove2.me/theorems/8f4f5679-7b99-41fe-a6d7-29a76d5829d8
-- title:
--   The rank budget contradiction for a finite quotient
-- statement:
--   For a finite group $F$, write $\rho(x)$ for the $F\times F$ permutation matrix of left multiplication, $\rho(x)_{a,b}=[a=xb]$. For $g:\iota\times\iota\to F$ the quotient matrix $Y(g)$ is the $(\iota\times F)\times(\iota\times F)$ block matrix with blocks $\rho(g(u,v))$. The family $g$ has surviving rectangles if $g(u,v)g(u',v)^{-1}g(u',v')g(u,v')^{-1}\ne1$ whenever $u\ne u'$ and $v\ne v'$. Let $q>r$ be prime, $P,I$ finite, $\mathrm{inc}:P\to\mathcal P(I)$, $f:P\times I\to\mathbb Z/q$ satisfying the line certificate
--   $$
--   \sum_{z:\ i\in\mathrm{inc}(z)}f(z,j)f(z,k)=-[j=k=i],
--   $$
--   and $g:I\times[r]^2\to F$ with every $g_i$ preserving rectangles. Suppose that for all $z$ outside a set $E\subseteq P$ the matrix $\sum_{i\in\mathrm{inc}(z)}Y(g_i)$ over $\mathbb Z/q$ has rank at most $2|F|$. Then the budget inequality $4(2|P|+r|E|)<|I|\,r$ is impossible.
--
--   Exceptional points are not deleted; their matrices are only bounded by their size $r|F|$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/MatrixRank.lean#L821-L862

import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank

open OAI OAI.Release075
universe u v
open scoped BigOperators

theorem OAI.Release075.finite_quotient_rank_obstruction {P I F : Type*} [Fintype P] [Fintype I]
    [DecidableEq I] [Group F] [Fintype F] [DecidableEq F]
    (r q : ℕ) [Fact q.Prime] (hq : r < q)
    (inc : P → Finset I) (f : P → I → ZMod q) (E : Finset P)
    (g : I → Fin r → Fin r → F) (hg : ∀ i, RectanglesSurvive (g i))
    (hline : ∀ i j k, (∑ z, if i ∈ inc z then f z j * f z k else 0) =
      -(if j = i ∧ k = i then 1 else 0))
    (hlocal : ∀ z, z ∉ E → (∑ i ∈ inc z, quotientMatrix (R := ZMod q) (g i)).rank ≤
      2 * Fintype.card F)
    (hbudget : 4 * (2 * Fintype.card P + r * E.card) < Fintype.card I * r) : False := by sorry
