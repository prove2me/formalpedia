-- Prove2me | Theorems.Thm_OAI_Release075_not_residuallyFinite_of_line_blocks
-- name    : OAI.Release075.not_residuallyFinite_of_line_blocks
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:38:15.826826+00:00
-- url     : https://prove2.me/theorems/a0ddce6a-3094-445f-b2ac-54105402483d
-- title:
--   Line blocks with surviving rectangles prevent residual finiteness
-- statement:
--   For a finite field $K$, a finite set $S\subseteq K$ and $a\in S^T$, the grid Lagrange function is $L_a(x)=\prod_{t\in T}\prod_{w\in S\setminus\{a_t\}}\frac{x_t-w}{a_t-w}$ on $K^T$. The punctured line through $a$ with direction $v\ne0$ is $\{a+xv:\ x\in K^{\times}\}$, and $\mathrm{inc}(z)$ is the set of labels $i$ whose punctured line through $a_i$ with direction $v_i$ contains $z$. Take $K=\mathbb Z/q$ with $q>r$ prime, distinct marks $a_i\in S^T$, directions $v_i\ne0$, and $2|T|(|S|-1)<q-1$. Let $G$ be a group with $g:I\times[r]^2\to G$ such that every $g_i$ has surviving rectangles. Suppose that for each point $z$ outside a set $E$, $\mathrm{inc}(z)$ splits into two disjoint Cartesian blocks on which $g$ satisfies the block relations $g(i,u,v)=L(u,c_1(i)+v)^{-1}R(v,c_2(i)+u)$. If
--   $$
--   4\bigl(2q^{|T|}+r|E|\bigr)<|I|\,r ,
--   $$
--   then $G$ is not residually finite.
--
--   This packages the finite rank obstruction into a statement about the group $G$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/MatrixRank.lean#L914-L938

import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank

open OAI OAI.Release075
universe u v
open scoped BigOperators

theorem OAI.Release075.not_residuallyFinite_of_line_blocks {T I G : Type*}
    [Fintype T] [Fintype I] [DecidableEq T] [DecidableEq I] [Group G]
    (r q : ℕ) [Fact q.Prime] (hq : r < q)
    (S : Finset (ZMod q)) (a v : I → T → ZMod q)
    (ha : ∀ i t, a i t ∈ S) (hinj : Function.Injective a) (hv : ∀ i, v i ≠ 0)
    (hdeg : 2 * (Fintype.card T * (S.card - 1)) < q - 1)
    (E : Finset (T → ZMod q)) (g : I → Fin r → Fin r → G)
    (hg : ∀ i, RectanglesSurvive (g i))
    (hblocks : ∀ z, z ∉ E → ∃ b₀ b₁ : CartesianBlock I r,
      Disjoint b₀.labels b₁.labels ∧ b₀.labels ∪ b₁.labels = lineIncidence a v z ∧
      b₀.Relations g ∧ b₁.Relations g)
    (hbudget : 4 * (2 * Fintype.card (T → ZMod q) + r * E.card) < Fintype.card I * r) :
    ¬ Group.ResiduallyFinite G := by sorry
