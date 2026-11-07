-- Prove2me | Theorems.Thm_OnlineCAP_theorem_1_3
-- name    : OnlineCAP.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:28:08.869565+00:00
-- url     : https://prove2.me/theorems/1aa093bf-8df7-496a-b58b-5b4c9dda0a87
-- title:
--   Theorem 1.3 — a randomized O(log n log log n)-competitive algorithm for OWCAP with cut arrivals
-- statement:
--   There is a function $\alpha(n)=O(\log n\,\log\log n)$ with the following property. Let $n\ge0$, $k\ge1$, let $G$ be a $k$-edge-connected multigraph on $V=\{v_0,\dots,v_{n-1}\}$, let $L\subseteq\binom V2$ be a set of links and $c:L\to\mathbb R_{\ge0}$ link costs. Then there is a randomized online algorithm for OWCAP with cut arrivals on $(G,L,c)$ that
--
--   1. buys only links of $L$, irrevocably;
--   2. after each arrival, crosses every $k$-cut requested so far, for every outcome of its coins;
--   3. satisfies, on every valid sequence $C_1,\dots,C_t$ of $k$-cuts chosen by an oblivious adversary,
--   $$\mathbb E\Big[\sum_{\ell\in F_t}c(\ell)\Big]\le\alpha(n)\cdot\mathrm{OPT}(C_1,\dots,C_t).$$
--
--   A sequence is valid when each requested cut is crossed by some link of $L$. This improves the $O(\log^2 n)$ ratio obtained from general online hitting set [Alo+09], and it also covers node arrivals.
--
--   **Formalization Note** The algorithm knows $G,L,c$ upfront and is chosen before the requests; the ratio depends on $n=|V|$ only.
--
--   Differences from the source:
--   - generalization: a k-edge-connected graph G = (V, E) → a k-edge-connected finite multigraph (parallel edges and loops allowed); reason: simple graphs are a special case; edge-connectivity augmentation is routinely posed for multigraphs
--   - reading: k-edge-connected (k unrestricted) → k ≥ 1; reason: the proof goes through Theorem 3.4, stated for connected graphs; for k = 0 the 0-cuts of a disconnected graph are unions of components, outside the paper's setting
--   - encoding: O(log n log log n)-competitive → α : ℕ → ℝ with α =O[atTop] log n · log log n, uniform over k, G, L, c and the requests; reason: §2: n = |V|; natural logarithms
--   - encoding: a sequence of k-cuts arriving online → every finite valid list of k-cuts (each crossed by some link of L), the purchases after a list depending only on it and the coins; reason: the guarantee at time t concerns the prefix; a cut no link crosses admits no feasible solution (Problem 2.4: F consists of non-empty sets)
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), Theorem 1.3, p.3 (proof §3.2, §4)

import Mathlib
import Definitions.Def_OnlineCAP_RandOnlineAlg
import Definitions.Def_OnlineCAP_OnlineHSInstance
import Definitions.Def_OnlineCAP_OnlineHSInstance_OPT
import Definitions.Def_OnlineCAP_IsCompetitive
import Definitions.Def_OnlineCAP_crosses
import Definitions.Def_OnlineCAP_edgeCut
import Definitions.Def_OnlineCAP_IsKCut
import Definitions.Def_OnlineCAP_capInstance
import Definitions.Def_OnlineCAP_IsKEdgeConnected

open MeasureTheory Filter Asymptotics

namespace OnlineCAP

/-- **Theorem 1.3 (randomized O(log n log log n)-competitive OWCAP with cut arrivals).** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…),
Theorem 1.3, p.3 (PDF p.3): "There is a randomized O(log n log log n)-competitive algorithm for
OWCAP with cut arrivals."

There is a function `α(n) = O(log n · log log n)` such that for every `n`, every `k ≥ 1`, every
k-edge-connected multigraph `G` on the vertices `v₀, …, v_{n−1}`, every set `L` of links (pairs of
distinct vertices) and every nonnegative cost function `c` on `L`, there is a randomized online
algorithm for OWCAP with cut arrivals on `(G, L, c)` that buys only links of `L`, crosses every
k-cut requested so far for every outcome of its coins, and is `α(n)`-competitive in expectation
against an oblivious adversary: `E[c(F_t)] ≤ α(n) · OPT` on every valid sequence of k-cuts.

**Formalization Note.** `n = |V|` (§2, p.9); the ratio depends on `n` only. The algorithm knows
`G, L, c` upfront and is chosen before the request sequence. Valid sequences consist of k-cuts
crossed by at least one link of `L`. `O(·)` is `Asymptotics.IsBigO` along `n → ∞`, natural
logarithms. -/
theorem theorem_1_3 : ∃ α : ℕ → ℝ,
    α =O[atTop] (fun n : ℕ => Real.log n * Real.log (Real.log n)) ∧
    ∀ (n k : ℕ), 1 ≤ k → ∀ (E : Type) [Fintype E] (ends : E → Sym2 (Fin n)),
      IsKEdgeConnected ends k → ∀ L : Finset (Sym2 (Fin n)), (∀ ℓ ∈ L, ¬ ℓ.IsDiag) →
      ∀ c : Sym2 (Fin n) → ℝ, (∀ ℓ ∈ L, 0 ≤ c ℓ) →
        ∃ A : RandOnlineAlg (Sym2 (Fin n)) (Finset (Fin n)),
          IsCompetitive (capInstance ends k L c) A (α n) := by sorry

end OnlineCAP
