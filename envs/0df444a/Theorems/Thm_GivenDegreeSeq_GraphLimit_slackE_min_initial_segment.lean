-- Prove2me | Theorems.Thm_GivenDegreeSeq_GraphLimit_slackE_min_initial_segment
-- name    : GivenDegreeSeq.GraphLimit.slackE_min_initial_segment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:43:20.057978+00:00
-- url     : https://prove2.me/theorems/26bee92c-0bda-4271-bef4-6733d7afe0c0
-- title:
--   §6.2, p. 30 — for nonincreasing $d$, $E(B)$ over $|B|=k$ is minimized at $B=\{1,\dots,k\}$
-- statement:
--   Let $d_1\ge d_2\ge\dots\ge d_n$ be real numbers and, for $B\subseteq\{1,\dots,n\}$,
--   $$E(B)=\sum_{j\notin B}\min\{d_j,|B|\}+|B|(|B|-1)-\sum_{i\in B}d_i.$$
--   Then for every $B$, with $k=|B|$,
--   $$E(\{1,\dots,k\})\le E(B).$$
--
--   This reduces the minimum of $E$ over all sets of a given size to an explicit expression in the sorted degrees, which converges to the continuum Erdős–Gallai functional of $f$ and so verifies the hypothesis of the MLE-existence lemma in the proof of Theorem 1.1.
--
--   **Formalization Note** In `Fin n` the initial segment of size $k$ is $\{i : i<k\}$; "nonincreasing" is `Antitone d`.
-- source:
--   Chatterjee, Diaconis & Sly, Random Graphs with a Given Degree Sequence, arXiv:1005.1136v5, p. 30 (§6.2, proof of Theorem 1.1, claim on E(B))

import Mathlib
import Definitions.Def_GivenDegreeSeq_GraphLimit_Phi

namespace GivenDegreeSeq.GraphLimit

/-- **§6.2, p. 30** (Chatterjee–Diaconis–Sly, arXiv:1005.1136v5). If `d_1 ≥ d_2 ≥ ⋯ ≥ d_n`, then
for each `k`, `E(B)` is minimized over all subsets `B` of size `k` at `B = {1, …, k}`. In `Fin n`
the initial segment of size `k = |B|` is `{i | i < k}` (the paper's vertex `i` is `i − 1`). -/
theorem slackE_min_initial_segment (n : ℕ) (d : Fin n → ℝ) (hd : Antitone d)
    (B : Finset (Fin n)) :
    slackE d (Finset.univ.filter (fun i : Fin n => (i : ℕ) < B.card)) ≤ slackE d B := by sorry

end GivenDegreeSeq.GraphLimit
