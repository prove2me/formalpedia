-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_Supplement_discovery_account
-- name    : NearlyOptimalPPR.Computation.Supplement.discovery_account
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:48:32.471533+00:00
-- url     : https://prove2.me/theorems/08212be3-2853-4731-836f-b3b15334ba6e
-- title:
--   Lemma 3.4 — global discovery and budget accounts
-- statement:
--   Fix a published exact-SDDM primitive model. Let $G$ be a finite simple unweighted undirected graph given by adjacency lists, $s$ a nonisolated seed, $0<\alpha\le1/2$, $0<\varepsilon\le1$, and $b$ any integer with $1\le b\le N=96/\varepsilon$. Put $q=\varepsilon/96$. Consider the prescribed Algorithm 5 execution, using the published depth-zero adapter and its operational ledger.
--
--   For any finite prefix write $H,x,r$ for the current active set, potential and work residual. Let $D_{\rm scan}$ be the sum of exterior-push row lengths actually scanned, $S=\sum d_vt$ over executed exterior pushes, and $W_{\rm all}$ the sum of actual incremental charges to all entered episodes, including a partial final episode. Then
--   $$r\ge0,\quad x\ge0,\quad\operatorname{vol}(H)\le N,\quad D_{\rm scan}\le\frac{23}{8}N,\quad S\le\frac38,\quad W_{\rm all}\le\frac{15}{8}.$$
--   The scan coefficient follows from the two numerical accounts in the printed proof. These are discovery scans; heap maintenance is charged separately in the companion theorem's total-work bound. The account bounds discovery over the entire run, without any assumption of termination.
--
--   Differences from the source:
--   - encoding: finite simple unweighted undirected adjacency-list graph, a seed, real parameters, and a positive integer block → the published InputGraph on Fin n with s : Fin n, real alpha and epsilon, and b : Nat with 1 <= b <= 96/epsilon; reason: finite labeling and positive natural blocks represent exactly the source inputs, including graphs with other isolated vertices
--   - encoding: Algorithm 5 with idealized exact FullSolve and CacheSolve operations → finite iteration of the published depth-zero recursive transition with threshold epsilon/96 and fixed schedule [b], plus the isolated-source wrapper and an erasing ledger; reason: root_threshold and coreRun_nonisolated prove the threshold and routine identities, run_core proves ledger erasure, and the theorem establishes that a legal block is not clamped
--   - encoding: valid finite execution prefixes and episodes → prefixes obtained only by iterating the operational transition, with recorded episode-entry and post-operation snapshots; reason: no residual, cache-size, termination or cost invariant is assumed; crossing updates and the current partial episode are retained
--   - encoding: O(N) exterior-push discovery cost in the p.12 degree-scan account → the sum of actually scanned exterior row lengths is at most 23N/8; reason: the proof bounds admitting scans by N and nonadmitting scans by 5S/q with S <= 3/8; heap work remains in the full complexity theorem
-- source:
--   Rong-Hua Li, Quanqing Xu, Yichun Yang, Junjie Zhou, STOC 2027 submission #884 (October 2026), Lemma 3.4, p. 12 (printed = PDF); canonical source.pdf, sha256 17a68253bbd187a44704374a465f62c34c8d7628c44b48c160e903ed3300bdb4

import Definitions.Def_NearlyOptimalPPR_Computation_Supplement_ledger

set_option autoImplicit false

namespace NearlyOptimalPPR.Computation.Supplement

/-- Li, Xu, Yang, Zhou, STOC 2027 submission #884 (October 2026),
Lemma 3.4 p.12. The explicit scan coefficient is 1 + 5*(3/8) = 23/8.
Heap-augmented work is kept separate from this discovery account. -/
theorem discovery_account (m : SolveModel) (n : ℕ) (g : InputGraph n) (s : Fin n)
    (α ε : ℝ) (b : ℕ) (hα : 0 < α) (hαhalf : α ≤ 1 / 2)
    (hε : 0 < ε) (hεone : ε ≤ 1) (hb : 1 ≤ b) (hbN : (b : ℝ) ≤ scale ε)
    (hs : 0 < g.graph.degree s) (t : ℕ) :
    let l := run m g s α ε b t
    (∀ v, 0 ≤ (l.core.frames 0).residual v ∧ 0 ≤ l.core.x v) ∧
    (volumeNat g (l.core.frames 0).active : ℝ) ≤ scale ε ∧
    (l.scans : ℝ) ≤ (23 / 8 : ℝ) * scale ε ∧
    l.pushMass ≤ 3 / 8 ∧ l.episodeCharges ≤ 15 / 8 := by sorry

end NearlyOptimalPPR.Computation.Supplement
