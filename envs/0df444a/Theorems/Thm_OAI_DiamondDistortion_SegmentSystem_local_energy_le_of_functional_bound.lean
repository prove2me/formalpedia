-- Prove2me | Theorems.Thm_OAI_DiamondDistortion_SegmentSystem_local_energy_le_of_functional_bound
-- name    : OAI.DiamondDistortion.SegmentSystem.local_energy_le_of_functional_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:41:17.479162+00:00
-- url     : https://prove2.me/theorems/215f43a3-d189-486a-81a3-d88a5bde0035
-- title:
--   A functional bounded on a local Euclidean block controls the block's segment energy
-- statement:
--   Let $\iota$ be a set and let $\mathcal{T}$ be a *segment system* on $\iota$: a distinguished collection of finite subsets of $\iota$, called *segments*, which contains every singleton. Fix a finite set $K\subseteq\iota$ and a *local family* $\mathcal{F}$ on $K$: a set of pairwise disjoint segments, each contained in $K$. Give $\mathbb{R}^{\mathcal{F}}$ the Euclidean norm $\|a\|_2=(\sum_{S\in\mathcal{F}}a_S^2)^{1/2}$ and define the linear map $L_{\mathcal{F}}:\mathbb{R}^{\mathcal{F}}\to\mathbb{R}^K$ by $(L_{\mathcal{F}}a)(v)=\sum_{S\in\mathcal{F},\ v\in S}a_S$ for $v\in K$; thus $L_{\mathcal{F}}a$ takes the value $a_S$ on each $S\in\mathcal{F}$ and vanishes on the rest of $K$. For $v\in K$ let $\delta_v\in\mathbb{R}^K$ be the indicator of $v$.
--
--   Let $f:\mathbb{R}^K\to\mathbb{R}$ be a linear functional and $u\ge0$ a real number such that $f(L_{\mathcal{F}}a)\le u$ for every $a\in\mathbb{R}^{\mathcal{F}}$ with $\|a\|_2\le1$. Then
--   $$
--   \sum_{S\in\mathcal{F}}\Big(\sum_{v\in S}f(\delta_v)\Big)^2\le u^2 .
--   $$
--
--   In words: if a functional on coordinates over $K$ is at most $u$ on the image of the Euclidean unit ball of the block $\mathcal{F}$, then the vector of its segment sums over $\mathcal{F}$ has Euclidean norm at most $u$. This is the finite duality step that turns a bound for a functional on local atoms into an energy bound of the kind that appears in the definition of the segment norm.
--
--   **Formalization Note** The local family is an element of `T.LocalFamily K` (a finite set of finite subsets of $K$), $\mathbb{R}^K$ is `T.Coordinates K`, $L_{\mathcal{F}}$ is `T.localMap F`, and $f$ is given as a continuous linear map (automatic in finite dimension). The Lean conclusion writes the inner sum as $\sum_{v\in S}\tilde b(v)$, where $\tilde b$ is the extension by zero to $\iota$ of $w\mapsto f(\delta_w)$ (`T.coordinateTest`); since $S\subseteq K$ this equals $\sum_{v\in S}f(\delta_v)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/SegmentNorm.lean#L812-L845

import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm

open OAI OAI.DiamondDistortion OAI.DiamondDistortion.SegmentSystem
universe u v
open scoped BigOperators Classical Topology
open Set
variable {ι : Type*} (T : SegmentSystem ι)
variable {T}
variable (T)
variable {T}
variable (T)

theorem OAI.DiamondDistortion.SegmentSystem.local_energy_le_of_functional_bound {K : Finset ι} (F : T.LocalFamily K)
    (f : T.Coordinates K →L[ℝ] ℝ) {u : ℝ} (hu : 0 ≤ u)
    (hf : ∀ a : EuclideanSpace ℝ (T.LocalIndex F), ‖a‖ ≤ 1 →
      f (T.localMap F a) ≤ u) :
    (∑ S : T.LocalIndex F, (∑ v ∈ S.val,
      T.coordinateTest K (fun w => f (Pi.single w 1)) v) ^ 2) ≤ u ^ 2 := by sorry
