-- Prove2me | Theorems.Thm_NAMatchEst_truncTrial_error
-- name    : NAMatchEst.truncTrial_error
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-23T00:58:25.025803+00:00
-- url     : https://prove2.me/theorems/d13e02c0-60a2-448e-abba-3f0db3302ff9
-- title:
--   Error of one truncated trial is at most $1/5$
-- statement:
--   Fix the standing setup of §3.2: $n$ larger than a universal constant $N_0$, a real $\alpha$ with $n^{1/3}\le\alpha\le n^{1/2}$ and an integer $k$ with $\alpha\le k\le n$. Run one **truncated trial** at scale $k$: the large-scale trial if $k>\alpha^2$ and the small-scale trial otherwise, aborted with answer No (and no queries) whenever one of its two Bernoulli vertex samples $S$, of inclusion probability $p$, has $|S|>\lceil 2np+100L\rceil$, where $L=\ln(2n)$. Then for every simple graph $G$ on $n$ vertices and every ordering of its adjacency lists:
--
--   1. if $\mu(G)\ge k$, the trial answers No with probability at most $1/5$;
--   2. if $\mu(G)<k/(C_0\alpha)$ with $C_0=2^{20}$, the trial answers Yes with probability at most $1/5$.
--
--   This is the per-trial guarantee that the gap tester of Lemma 3.1 amplifies by a majority vote over $O(\log n)$ independent truncated trials: the untruncated trials err with probability at most $1/10$ (Lemmas 3.12 and 3.13), and the caps are exceeded only with tiny probability, which matters only in the yes-case because an aborted trial answers No.
--
--   **Formalization Note** The truncated trial is `truncTrial n α k`; Yes is `true`. One threshold $N_0$ is chosen before $n$, $\alpha$, $k$ and $G$.
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation (STOC 2027 submission), §3.9, p.29–30 (PDF 33–34) (the caps (24) fail with probability n^{-Ω(1)}) and proof of Lemma 3.1, p.31 (PDF 35), combining Lemmas 3.12 and 3.13 with the cap analysis before majority amplification.

import Mathlib
import Definitions.Def_TuranMatching_Clique_Setting
import Definitions.Def_NAMatchEst_AdjList
import Definitions.Def_NAMatchEst_AdjList_toGraph
import Definitions.Def_NAMatchEst_RandAlg
import Definitions.Def_NAMatchEst_RandAlg_prob
import Definitions.Def_NAMatchEst_C0
import Definitions.Def_NAMatchEst_truncTrial

namespace NAMatchEst

theorem truncTrial_error : ∃ N₀ : ℕ, ∀ (n : ℕ) [NeZero n], N₀ ≤ n → ∀ (α : ℝ) (k : ℕ),
    (n : ℝ) ^ ((1 : ℝ) / 3) ≤ α → α ≤ (n : ℝ) ^ ((1 : ℝ) / 2) → α ≤ k → (k : ℝ) ≤ n →
    ∀ G : AdjList n,
      (k ≤ TuranMatching.Clique.matchingNumber G.toGraph →
        (truncTrial n α k).prob G (· = false) ≤ 1 / 5) ∧
      ((TuranMatching.Clique.matchingNumber G.toGraph : ℝ) < k / (C0 * α) →
        (truncTrial n α k).prob G (· = true) ≤ 1 / 5) := by sorry

end NAMatchEst
