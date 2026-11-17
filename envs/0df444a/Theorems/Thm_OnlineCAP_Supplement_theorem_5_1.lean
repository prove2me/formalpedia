-- Prove2me | Theorems.Thm_OnlineCAP_Supplement_theorem_5_1
-- name    : OnlineCAP.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:23:17.666195+00:00
-- url     : https://prove2.me/theorems/e697f2ea-70d0-4eba-ab53-e6b534bf94df
-- title:
--   Theorem 5.1 — a deterministic 10-competitive algorithm for OCycAP with node arrivals
-- statement:
--   Let $n\ge0$ and let $L$ be a set of links (pairs of distinct vertices) on the cycle $R=v_0v_1\cdots v_{n-1}v_0$, each of cost $1$. There is a deterministic online algorithm that receives terminal pairs $(s_1,t_1),(s_2,t_2),\dots$ of distinct vertices, buys only links of $L$, makes every revealed pair 3-edge-connected in $R+F_t$, and on every valid sequence of pairs buys
--
--   $$|F_t|\le 10\cdot\mathrm{OPT}\big((s_1,t_1),\dots,(s_t,t_t)\big)$$
--
--   links, where $\mathrm{OPT}$ is the least number of links of $L$ satisfying all requested pairs.
--
--   Together with Theorem 5.4 this separates node arrivals from cut arrivals on cycles: constant ratio for the former, $\Omega(\log n)$ for the latter.
--
--   Differences from the source:
--   - encoding: terminal pairs (s_t, τ_t) ∈ (V choose 2) made 3-edge-connected in the cycle plus F_t; deterministic ratio 10 → ordered pairs of distinct vertices; satisfaction in cut form (PairSat (cycleEnds n) 2, every separating set has ≥ 3 crossing edges and links); valid = each pair satisfiable by L; OPT_node as sInf; a RandOnlineAlg with IsDeterministic and expected cost ≤ 10 · OPT; reason: Problem 2.3 states satisfaction in this cut form; for a deterministic algorithm the expectation is the cost; same instances
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), Theorem 5.1, p.21 (PDF p.21); §5.1, pp.21–23; Problem 2.3, p.9

import Mathlib
import Definitions.Def_OnlineCAP_RandOnlineAlg
import Definitions.Def_OnlineCAP_RandOnlineAlg_IsDeterministic
import Definitions.Def_OnlineCAP_crosses
import Definitions.Def_OnlineCAP_edgeCut
import Definitions.Def_OnlineCAP_cycleEnds
import Definitions.Def_OnlineCAP_Supplement_PairSat
import Definitions.Def_OnlineCAP_Supplement_IsNodeCompetitive

open MeasureTheory

namespace OnlineCAP.Supplement

/-- **Theorem 5.1 (deterministic 10-competitive OCycAP with node arrivals).** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online
Connectivity Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…),
Theorem 5.1, p.21 (PDF p.21): "There is a deterministic 10-competitive algorithm for OCycAP with
node arrivals."

For every `n` and every set `L` of links (pairs of distinct vertices) on the cycle
`v₀ v₁ ⋯ v_{n−1} v₀` with unit costs, there is a deterministic online algorithm that receives
terminal pairs `(s, t)`, `s ≠ t`, buys only links of `L`, makes every revealed pair
3-edge-connected in the cycle plus the purchased links, and buys at most `10 · OPT` links on every
valid sequence of pairs, where `OPT` is the least number of links of `L` satisfying all of them.

**Formalization Note.** "OCycAP" is the unweighted problem on a cycle, `k = 2` (Problems 2.2–2.3,
p.9); satisfaction is the cut form of Problem 2.3 (`PairSat`). A sequence is valid when each pair
consists of distinct vertices and is satisfied by `L`. The constant is exactly `10`, with no
additive term. The cycle is the standard labelled cycle. -/
theorem theorem_5_1 (n : ℕ) (L : Finset (Sym2 (Fin n))) (hL : ∀ ℓ ∈ L, ¬ ℓ.IsDiag) :
    ∃ A : RandOnlineAlg (Sym2 (Fin n)) (Fin n × Fin n), A.IsDeterministic ∧
      IsNodeCompetitive (cycleEnds n) 2 L (fun _ => 1) A 10 := by sorry

end OnlineCAP.Supplement
