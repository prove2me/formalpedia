-- Prove2me | Theorems.Thm_OAI_DiamondDistortion_SegmentSystem_test_energy_le_allow_empty
-- name    : OAI.DiamondDistortion.SegmentSystem.test_energy_le_allow_empty
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:38:04.456105+00:00
-- url     : https://prove2.me/theorems/965f64ba-f791-4935-be1d-f5956e1d9b89
-- title:
--   Disjoint segment families with empty pieces are dominated by the segment norm
-- statement:
--   Let $\iota$ be a set and let $\mathcal{T}$ be a *segment system* on $\iota$: a distinguished collection of finite subsets of $\iota$, called *segments*, which contains every singleton $\{v\}$, $v\in\iota$ (nothing is assumed about the empty set). For a finitely supported function $u:\iota\to\mathbb{R}$, its *segment norm* is
--   $$
--   \|u\|_{\mathcal{T}}=\sup\Big\{\Big(\sum_{k=1}^{n}\Big(\sum_{v\in S_k}u(v)\Big)^2\Big)^{1/2}\ :\ n\in\mathbb{N},\ S_1,\dots,S_n\ \text{pairwise disjoint segments}\Big\}.
--   $$
--
--   Let $\kappa$ be a finite index set and let $(S_g)_{g\in\kappa}$ be finite subsets of $\iota$ that are pairwise disjoint ($S_g\cap S_h=\emptyset$ for $g\neq h$) and such that every nonempty $S_g$ is a segment. Then for every finitely supported $u:\iota\to\mathbb{R}$,
--   $$
--   \sum_{g\in\kappa}\Big(\sum_{v\in S_g}u(v)\Big)^2\le\|u\|_{\mathcal{T}}^2 .
--   $$
--
--   So the supremum defining the segment norm may be tested on disjoint families indexed by any finite set, and empty pieces are allowed even when the empty set is not a segment. Such empty pieces arise naturally when segments are cut or restricted (for instance to a head), and this form of the estimate is the one invoked by the dual-norm bounds and splitting estimates for segment norms.
--
--   **Formalization Note** A segment system is a structure `SegmentSystem` consisting of a predicate `IsSegment` on finite sets together with the singleton axiom. The segment norm is `T.primalSeminorm`, defined as the supremum of the seminorms attached to represented families `T.Family` (lists of pairwise disjoint segments indexed by `Fin n`); the supremum is finite because every test is bounded by $\sum_v|u(v)|$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/SegmentNorm.lean#L152-L169

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

theorem OAI.DiamondDistortion.SegmentSystem.test_energy_le_allow_empty {κ : Type*} [Fintype κ] (S : κ → Finset ι)
    (hS : ∀ i, (S i).Nonempty → T.IsSegment (S i))
    (hd : Pairwise (fun i j => Disjoint (S i) (S j))) (u : ι →₀ ℝ) :
    (∑ i, (∑ v ∈ S i, u v) ^ 2) ≤ (T.primalSeminorm u) ^ 2 := by sorry
