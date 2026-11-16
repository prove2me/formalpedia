-- Prove2me | Theorems.Thm_LowDiameterNashWilliams_Main_Supplement_theorem_7
-- name    : LowDiameterNashWilliams.Main.Supplement.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:44:01.986322+00:00
-- url     : https://prove2.me/theorems/b50b3f74-8506-4baa-980b-c06f716bf734
-- title:
--   Theorem 7 (companion theorem; not used in the proof of the goal) — Internal-vertex gap hardness
-- statement:
--   There exists a positive integer $k_0$ such that, for every fixed integer $k\ge k_0$, it is NP-hard to distinguish the following cases for an $n$-vertex finite simple graph $G$ promised to contain $k$ pairwise edge-disjoint spanning trees:
--   $$\mathrm{YES}:\quad\exists(T_i)_{i=1}^k\text{ a packing},\ \forall i,\ |\operatorname{int}(T_i)|<\frac{3n}{\delta(G)},$$
--   $$\mathrm{NO}:\quad\forall T\text{ spanning tree of }G,\ |\operatorname{int}(T)|>\frac{n\ln\delta(G)}{600\delta(G)}.$$
--   Both inequalities are strict. The NO case includes every spanning tree. The fixed parameter precedes varying graph data, and a reduction may depend on it. This theorem is an independent companion to Theorem 1.
--
--   Differences from the source:
--   - encoding: finite simple unweighted graphs with unordered edges → labelled finite endpoint arrays with the published simplicity and spanning-tree predicates; reason: every finite graph is represented up to relabelling; each unordered edge is counted once
--   - encoding: diameter and minimum-degree ratios on the graph packing promise → at least two vertices in each graph hardness promise; reason: these are the nondegenerate inputs on which the source ratios are defined; the promise then implies positive minimum degree
--   - encoding: NP-hardness for every fixed parameter → GapNPHard of explicit self-delimiting binary input codes using CookPvsNP polynomial-time machines; reason: this is polynomial-time many-one promise hardness; all validity constraints occur on both output sides and reductions may depend on the fixed parameter
-- source:
--   Pin-Hsian Lee, Peng-Ting Lin, Meng-Tsung Tsai, Ting-An Wu, STOC 2027 submission #1510 (October 2026), Theorem 7, p. 28 (PDF p. 29)

import Mathlib
import Definitions.Def_LowDiameterNashWilliams_Main_Supplement_Promises

set_option autoImplicit false
open scoped ENNReal NNReal
open scoped BigOperators
open Classical
open LowDiameterNashWilliams.Main
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn
open SetCoverThreshold.SetCover

namespace LowDiameterNashWilliams.Main.Supplement

theorem theorem_7 :
    ∃ k₀ : ℕ, 0 < k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      GapNPHard GraphInput.encode (InternalYes k) (InternalNo k) := by sorry

end LowDiameterNashWilliams.Main.Supplement
