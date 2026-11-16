-- Prove2me | Theorems.Thm_GaussianSweep_Supplement_theorem_3_6
-- name    : GaussianSweep.Supplement.theorem_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:39:50.930648+00:00
-- url     : https://prove2.me/theorems/7cf98f63-1b51-4df4-9335-52d9153bfbfb
-- title:
--   Theorem 3.6 — cut sweep for $\Delta \le p$: $\mathrm{pw} \le \mathrm{cw} \le \gamma_p m + \eta_p(n)$, with the $\Delta \le 4, 5$ bisection and cutwidth bounds
-- statement:
--   Let $\gamma_p = \arccos(2\sqrt{p-1}/p)/\pi$, and let $n$ and $m$ be the numbers of vertices and edges.
--
--   1. For every integer $p \ge 3$ there is a function $\eta_p(n) = o(n)$ such that every graph $G$ with $\Delta(G) \le p$ satisfies
--   $$
--   \mathrm{pw}(G) \le \mathrm{cw}(G) \le \gamma_p\, m + \eta_p(n).
--   $$
--   2. The bisection width and the cutwidth of every graph $G$ with $\Delta(G) \le 4$ are at most $m/6 + o(n)$, and $m/6 \le n/3$.
--   3. The bisection width and the cutwidth of every graph $G$ with $\Delta(G) \le 5$ are at most $\gamma_5 m + o(n)$, $\gamma_5 m \le \tfrac52\gamma_5 n$, and $\tfrac52 \gamma_5 < 0.5121$.
--
--   Each remainder is a function of $n$ alone ($\eta_p$ may depend on $p$), the same for all graphs in the class.
--
--   Differences from the source:
--   - encoding: η_p(n) = o(n) and the o(n) of the 'in particular' clauses → for each p ≥ 3, ∃ η with η(n)/n → 0 before the graph; one ∃ ρ for the Δ ≤ 4 clause and one for the Δ ≤ 5 clause; reason: the paper's remainder convention (p.1); η_p is chosen after p
--   - reading: at most m/6 + o(n) ≤ n/3 + o(n) → bw ≤ m/6 + ρ(n), cw ≤ m/6 + ρ(n), and m/6 ≤ n/3; reason: the chain compares the same o(n) term on both sides, so its content is m/6 ≤ n/3
--   - reading: at most γ5 m + o(n) ≤ (5/2)γ5 n + o(n) < 0.5121n + o(n) → bw, cw ≤ γ5 m + ρ(n), γ5 m ≤ (5/2)γ5 n, and (5/2)γ5 < 0.5121; reason: a strict inequality between expressions carrying unspecified o(n) terms has content only as the comparison of the constants (5/2)γ5 < 0.5121, which is how the proof (p.20) states it
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Theorem 3.6, p.20 (PDF p.22)

import Mathlib
import Definitions.Def_GaussianSweep_pathwidth
import Definitions.Def_GaussianSweep_Supplement_cutwidth
import Definitions.Def_GaussianSweep_Supplement_bisectionWidth
import Definitions.Def_GaussianSweep_Supplement_gammaP
open Filter Topology

namespace GaussianSweep.Supplement

/-- Theorem 3.6 (cut sweep, maximum degree `p`) (Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Theorem 3.6, p.20
(PDF p.22)). For every integer `p ≥ 3` there is a function `η_p(n) = o(n)` such that every graph
`G` with `Δ(G) ≤ p` satisfies `pw(G) ≤ cw(G) ≤ γ_p m + η_p(n)`. In particular, the bisection
width and the cutwidth of every graph `G` with `Δ(G) ≤ 4` are at most `m/6 + o(n) ≤ n/3 + o(n)`,
and those of every graph `G` with `Δ(G) ≤ 5` are at most
`γ₅ m + o(n) ≤ (5/2)γ₅ n + o(n) < 0.5121 n + o(n)`.

**Formalization Note** `m = |E(G)|` is `G.edgeSet.ncard`, `n = |V|`. The remainder `η_p`
depends on `p` only (chosen after `p`, before the graph). The "in particular" clauses are
conjuncts (2) and (3), each with its own remainder `ρ`: the chain `m/6 + o(n) ≤ n/3 + o(n)` is
`m/6 ≤ n/3` with the same remainder on both sides, `γ₅ m + o(n) ≤ (5/2)γ₅ n + o(n)` is
`γ₅ m ≤ (5/2)γ₅ n`, and the strict `(5/2)γ₅ n + o(n) < 0.5121 n + o(n)` is the constant
comparison `(5/2)γ₅ < 0.5121` (a strict inequality between two unspecified `o(n)` terms has no
other content). -/
theorem theorem_3_6 :
    (∀ p : ℕ, 3 ≤ p → ∃ η : ℕ → ℝ, Tendsto (fun n => η n / n) atTop (𝓝 0) ∧
      ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj], G.maxDegree ≤ p →
        GaussianSweep.pathwidth G ≤ (cutwidth G : ℤ) ∧
          (cutwidth G : ℝ) ≤ gammaP p * G.edgeSet.ncard + η (Fintype.card V)) ∧
    (∃ ρ : ℕ → ℝ, Tendsto (fun n => ρ n / n) atTop (𝓝 0) ∧
      ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj], G.maxDegree ≤ 4 →
        (bisectionWidth G : ℝ) ≤ (G.edgeSet.ncard : ℝ) / 6 + ρ (Fintype.card V) ∧
        (cutwidth G : ℝ) ≤ (G.edgeSet.ncard : ℝ) / 6 + ρ (Fintype.card V) ∧
        (G.edgeSet.ncard : ℝ) / 6 ≤ (Fintype.card V : ℝ) / 3) ∧
    (∃ ρ : ℕ → ℝ, Tendsto (fun n => ρ n / n) atTop (𝓝 0) ∧
      ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj], G.maxDegree ≤ 5 →
        (bisectionWidth G : ℝ) ≤ gammaP 5 * G.edgeSet.ncard + ρ (Fintype.card V) ∧
        (cutwidth G : ℝ) ≤ gammaP 5 * G.edgeSet.ncard + ρ (Fintype.card V) ∧
        gammaP 5 * G.edgeSet.ncard ≤ 5 / 2 * gammaP 5 * Fintype.card V) ∧
    5 / 2 * gammaP 5 < 0.5121 := by sorry

end GaussianSweep.Supplement
