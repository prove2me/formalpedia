-- Prove2me | Theorems.Thm_HighPrecSAC1_Main_lemma_3_3
-- name    : HighPrecSAC1.Main.lemma_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:29:12.242014+00:00
-- url     : https://prove2.me/theorems/3e3893e9-d796-436f-907b-1da5275e6b3a
-- title:
--   Lemma 3.3 — recursive layer approximation
-- statement:
--   For every nonnegative initial vector and every sequence of positive quadratic layer maps, let $b_k(t)$ be the recursion of Section 3.2: $b_0(t)=x_0$, and at layer $k>0$ use $u=\lceil t/2\rceil$, $\ell=\min\{k,u+3\}$, the earlier outputs at precisions $u+2j$, the ordered Jacobian products in (3.3)–(3.4), evaluator accuracy $q=t+\ell+3$, and downward rounding to $t+2$ bits as in (3.5). Any local evaluator satisfying the stated directed relative-error guarantees is permitted. Then for every $0\le k\le K$ and $t\ge1$,
--   $$(1-2^{-t})x_k\le b_k(t)\le x_k.$$
--   This includes the circuit-derived construction and preserves its full recursive dependency on all earlier accuracies.
--
--   Differences from the source:
--   - encoding: finite circuits, Boolean strings, vectors and entrywise matrix inequalities → Fin-indexed words and gates, real vectors, and the explicit EntryLE matrix relation; reason: these carriers preserve the finite objects and the componentwise order
--   - generalization: the circuit-derived layer maps and local choices furnished by Lemma 3.2 → any nonnegative initial vector, positive quadratic layer maps and local oracle satisfying the two approximation guarantees; reason: the original maps and evaluator are instances; the recursion is unchanged and the source proof uses only these guarantees
-- source:
--   Cheng, Huang and Wu (2026), arXiv:2610.25623 (preprint; held version, version number not printed in the PDF, sha256 8c9ac662…), Lemma 3.3, printed p. 15 (PDF 16)

import Definitions.Def_HighPrecSAC1_Main_Refinement

open scoped BigOperators Matrix

namespace HighPrecSAC1.Main

theorem lemma_3_3 :
    ∀ (K m : ℕ) (S : LayerSystem K m) (O : ApproxOracle m),
    S.positive → OracleValid O → ∀ k t, k ≤ K → 1 ≤ t →
      (1-err t) • S.values k ≤ recursiveApprox S O k t ∧
        recursiveApprox S O k t ≤ S.values k := by sorry

end HighPrecSAC1.Main
