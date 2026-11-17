-- Prove2me | Theorems.Thm_OnlineCAP_Supplement_theorem_1_4
-- name    : OnlineCAP.Supplement.theorem_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:21:31.225874+00:00
-- url     : https://prove2.me/theorems/800c06e8-2958-45db-9cdc-bfb37f0a6de4
-- title:
--   Theorem 1.4 — a deterministic $O(\log n)$-competitive algorithm for unweighted OCAP with cut arrivals
-- statement:
--   There is a function $\alpha(n)=O(\log n)$ with the following property. Let $n\ge0$, $k\ge1$, let $G$ be a $k$-edge-connected multigraph on the vertices $v_0,\dots,v_{n-1}$, and let $L$ be a set of links (pairs of distinct vertices), each of cost $1$. Then there is a deterministic online algorithm for OCAP with cut arrivals on $(G,L)$ that buys only links of $L$, crosses every $k$-cut requested so far, and on every valid sequence $C_1,\dots,C_t$ of $k$-cuts buys
--
--   $$|F_t|\le\alpha(n)\cdot\mathrm{OPT}(C_1,\dots,C_t)$$
--
--   links, where $\mathrm{OPT}$ is the least number of links of $L$ crossing all requested cuts.
--
--   The ratio is optimal up to the constant and matches the node-arrival result of Garg and Subramanian; with Theorem 1.3 it shows that unweighted cut arrivals cost no more than node arrivals on general graphs.
--
--   Differences from the source:
--   - reading: "an O(log n)-competitive algorithm" (deterministic or randomized not stated) → a deterministic algorithm (A.IsDeterministic); reason: the proof (Algorithm 1 with the deterministic subroutines of Theorem 1.11, then Proposition 3.5) is deterministic, and the paper writes "randomized" only for Theorem 1.3; this is the stronger reading
--   - encoding: k-edge-connected graph G with |V| = n, links L ⊆ (V choose 2), unit costs, ratio O(log n) → multigraph ends : E → Sym2 (Fin n), k ≥ 1, L without diagonal pairs, c ≡ 1, ∃ α =O[atTop] Real.log with ratio α n, finite valid request lists, OPT as sInf; reason: the published model of the mission goal OnlineCAP.theorem_1_3; same instances
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), Theorem 1.4, p.3 (PDF p.3); proof via Theorem 3.3 and Proposition 3.5, pp.12–13

import Mathlib
import Definitions.Def_OnlineCAP_RandOnlineAlg
import Definitions.Def_OnlineCAP_RandOnlineAlg_IsDeterministic
import Definitions.Def_OnlineCAP_OnlineHSInstance
import Definitions.Def_OnlineCAP_OnlineHSInstance_OPT
import Definitions.Def_OnlineCAP_IsCompetitive
import Definitions.Def_OnlineCAP_crosses
import Definitions.Def_OnlineCAP_edgeCut
import Definitions.Def_OnlineCAP_IsKCut
import Definitions.Def_OnlineCAP_capInstance
import Definitions.Def_OnlineCAP_IsKEdgeConnected

open MeasureTheory Filter Asymptotics

namespace OnlineCAP.Supplement

/-- **Theorem 1.4 (O(log n)-competitive unweighted OCAP with cut arrivals).** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online
Connectivity Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…),
Theorem 1.4, p.3 (PDF p.3): "There is an O(log n)-competitive algorithm for unweighted OCAP under
cut arrivals."

There is a function `α(n) = O(log n)` such that for every `n`, every `k ≥ 1`, every
k-edge-connected multigraph on the vertices `v₀, …, v_{n−1}` and every set `L` of links (pairs of
distinct vertices) with unit costs, there is a deterministic online algorithm for OCAP with cut
arrivals that buys only links of `L`, crosses every requested k-cut, and buys at most
`α(n) · OPT` links on every valid sequence of k-cuts.

**Formalization Note.** Same model as the mission goal `OnlineCAP.theorem_1_3`, with costs
`c ≡ 1` and the algorithm required to be deterministic (the paper's proof, Algorithm 1 and
Proposition 3.5, is deterministic; it calls only Theorem 1.3 randomized). The ratio depends on
`n` only; the algorithm is chosen before the request sequence. `O(·)` is `IsBigO` along
`n → ∞`, natural logarithm. -/
theorem theorem_1_4 : ∃ α : ℕ → ℝ, α =O[atTop] (fun n : ℕ => Real.log n) ∧
    ∀ (n k : ℕ), 1 ≤ k → ∀ (E : Type) [Fintype E] (ends : E → Sym2 (Fin n)),
      IsKEdgeConnected ends k → ∀ L : Finset (Sym2 (Fin n)), (∀ ℓ ∈ L, ¬ ℓ.IsDiag) →
        ∃ A : RandOnlineAlg (Sym2 (Fin n)) (Finset (Fin n)), A.IsDeterministic ∧
          IsCompetitive (capInstance ends k L (fun _ => 1)) A (α n) := by sorry

end OnlineCAP.Supplement
