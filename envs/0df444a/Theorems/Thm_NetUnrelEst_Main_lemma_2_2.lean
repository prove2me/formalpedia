-- Prove2me | Theorems.Thm_NetUnrelEst_Main_lemma_2_2
-- name    : NetUnrelEst.Main.lemma_2_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T07:16:11.828696+00:00
-- url     : https://prove2.me/theorems/131b9a0c-69d3-4653-84a7-5e6d5a81f3f6
-- title:
--   Lemma 2.2 — the recursion is nonnegative and unbiased, with EW² ≤ 2Σ2^{−j}E(U_j r_j) ≤ 4µ(D) for every cut rule
-- statement:
--   Let $G$ be a connected multigraph with $n\ge2$ vertices, $\mu$ a product law with failure probabilities $q_e\in[0,1]$, and $0=t_0<\dots<t_h=1$ a fixed time sequence. Let $W$ be the return of Algorithm 2.1 started at time zero with $A=\emptyset$, using any valid cut rule (a cut of the current graph chosen with fresh randomness). Then $W\ge0$, $\mathbb EW=\mu(D)$, and
--   $$\mathbb EW^2\le 2\sum_{j=0}^{h}2^{-j}\,\mathbb E(U_jr_j)\le 4\mu(D),\tag{6}$$
--   where $U_j$ and $r_j$ are the conditional unreliability and the residual probability outside the stored union at depth $j$ of the extended random path.
--
--   This is the second-moment identity behind the recursive estimator: it holds for every cut rule. The term $U_jr_j$ is what Theorem 3.5 bounds, and it can be much smaller than $U_j^2$ when the chosen cut carries most of the disconnection probability.
--
--   **Formalization Note.** $W$ is a finite `PMF` on $\mathbb R$; $W\ge0$ means every value in its support is nonnegative. The mean and the second moment are integrals against its measure, and integrability of $W$ and $W^2$ is part of the conclusion. $\mathbb E(U_jr_j)$ is the mean of $U_jr_j$ under the law of the path at depth $j$.
--
--   Differences from the source:
--   - generalization: the graph G of §2.1 (the reduced graph: no self-loops, no parallel edges, n ≥ n₀) → any connected multigraph on Fin n with n ≥ 2 (self-loops and parallel edges allowed); reason: Algorithm 2.1 and the proof use only the product law and the cut structure, on which loops have no effect and parallel edges act as one edge with the product failure probability; the reduced graph is one instance
--   - generalization: a rule that selects a cut from the current graph and independent fresh randomness → a law on cuts that may depend on the level j, the arrived set (the current graph) and the stored cuts, returning a cut of the current graph whenever it has two or more vertices; reason: every rule of the paper is such a law; the proof uses only that each call's cut is a cut of its graph chosen independently of later randomness
--   - encoding: the return W of Algorithm 2.1 and its moments → a finite PMF built by recursion on the remaining levels; EW and EW² as integrals against PMF.toMeasure, with integrability of W and W² added to the conclusion; reason: the laws are finite, so W and W² are integrable and the integrals are the paper's expectations
--   - encoding: U_j, r_j along a uniformly random root path of the full binary tree, observations continued below terminated calls → one Markov trajectory (arrived set, stored cuts, alive flag) whose contraction continues after termination, with r_j = 0 once the call has terminated; reason: the two children of a call have the same conditional law, so a uniformly random path has this law
-- source:
--   Sun, Near-Linear Estimation of Network Unreliability, STOC 2027 submission, doi:10.5281/zenodo.23913531 (PDF sha256 eee2585a…), p. 10, Lemma 2.2

import Mathlib
import Definitions.Def_NetUnrelDesign_Main_Model
import Definitions.Def_NetUnrelEst_Main_CutSums
import Definitions.Def_NetUnrelEst_Main_Recursion

open scoped BigOperators ENNReal

open NetUnrelDesign.Main

namespace NetUnrelEst.Main

/-- **Lemma 2.2.** For every initial product law (failure probabilities `q ∈ [0,1]^m`), every finite
time sequence `0 = t₀ < ⋯ < t_h = 1` and every cut rule that returns a cut of the current graph
using fresh randomness, the return `W` of Algorithm 2.1 started with `A = ∅` satisfies `W ≥ 0`,
`EW = µ(D)` and `EW² ≤ 2 Σ_{j=0}^{h} 2^{−j} E(U_j r_j) ≤ 4µ(D)` (6), with `U_j, r_j` along the
extended random path. Sun 2027, p. 10, Lemma 2.2. -/
theorem lemma_2_2 {n m : ℕ} (ends : Ends n m) (hn : 2 ≤ n) (hconn : IsConnectedGraph ends)
    (q : Fin m → ℝ) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1) (h : ℕ) (t : ℕ → ℝ) (ht : TimeSeq h t)
    (rule : CutRule n m) (hrule : ValidRule ends rule) :
    (∀ x ∈ (retLaw ends q h t rule ∅).support, 0 ≤ x) ∧
    MeasureTheory.Integrable (fun x : ℝ => x) (retLaw ends q h t rule ∅).toMeasure ∧
    MeasureTheory.Integrable (fun x : ℝ => x ^ 2) (retLaw ends q h t rule ∅).toMeasure ∧
    pmfMean (retLaw ends q h t rule ∅) = unrel ends q ∧
    pmfSecondMoment (retLaw ends q h t rule ∅) ≤
      2 * ∑ j ∈ Finset.range (h + 1), ((2 : ℝ) ^ j)⁻¹ * pathMoment ends q t rule ∅ j ∧
    2 * ∑ j ∈ Finset.range (h + 1), ((2 : ℝ) ^ j)⁻¹ * pathMoment ends q t rule ∅ j ≤
      4 * unrel ends q := by sorry

end NetUnrelEst.Main
