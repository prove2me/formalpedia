-- Prove2me | Theorems.Thm_OAI_DiamondDistortion_FiniteAverage_joint_budget
-- name    : OAI.DiamondDistortion.FiniteAverage.joint_budget
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:37:07.609548+00:00
-- url     : https://prove2.me/theorems/6ca6b508-b60a-4e5f-94a8-bd63c976790b
-- title:
--   Averaged distance-plus-deficit budget for vectors with prescribed mean correlation
-- statement:
--   Let $\Omega$ be a finite set and $w:\Omega\to\mathbb{R}$ probability weights ($w(\omega)\ge0$ for all $\omega$ and $\sum_\omega w(\omega)=1$). For each $\omega\in\Omega$ let $I_\omega$ be a finite index set and let $a_\omega,b_\omega\in\mathbb{R}^{I_\omega}$; on $\mathbb{R}^{I_\omega}$ write $\langle x,y\rangle=\sum_{i\in I_\omega}x_iy_i$ and $\|x\|^2=\langle x,x\rangle$. Let $r,R\in\mathbb{R}$ and assume
--
--   1. $\|a_\omega\|^2\le R^2$ for every $\omega\in\Omega$, and
--   2. $\sum_{\omega\in\Omega}w(\omega)\langle a_\omega,b_\omega\rangle=r^2$.
--
--   Then
--   $$
--   \sum_{\omega\in\Omega}w(\omega)\,\|a_\omega-b_\omega\|^2+\sum_{\omega\in\Omega}w(\omega)\big(r^2-\|b_\omega\|^2\big)\le R^2-r^2 .
--   $$
--
--   If the vectors $a_\omega$ have energy at most $R^2$ and their average correlation with the $b_\omega$ equals $r^2$, the slack $R^2-r^2$ jointly controls the average squared distance between $a_\omega$ and $b_\omega$ and the average energy deficit $r^2-\|b_\omega\|^2$ (the second term may be negative, so only the sum is bounded). The index sets $I_\omega$ may differ from one outcome to another.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/FiniteAverage.lean#L127-L161

import Mathlib
import Definitions.Def_DiamondDistortion

open OAI OAI.DiamondDistortion
universe u v
open scoped BigOperators Classical Topology
open Set
variable {Ω : Type*} [Fintype Ω]

theorem OAI.DiamondDistortion.FiniteAverage.joint_budget (w : Ω → ℝ) (hw : ∀ ω,0 ≤ w ω) (hs : ∑ ω,w ω=1)
    (I : Ω → Type*) [∀ ω,Fintype (I ω)] (a b : ∀ ω,I ω→ℝ) {r R : ℝ}
    (he : ∀ ω,(∑ i,a ω i^2) ≤ R^2)
    (hc : (∑ ω,w ω*(∑ i,a ω i*b ω i)) = r^2) :
    (∑ ω,w ω*(∑ i,(a ω i-b ω i)^2)) +
      (∑ ω,w ω*(r^2-∑ i,b ω i^2)) ≤ R^2-r^2 := by sorry
