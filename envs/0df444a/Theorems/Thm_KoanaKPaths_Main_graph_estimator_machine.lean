-- Prove2me | Theorems.Thm_KoanaKPaths_Main_graph_estimator_machine
-- name    : KoanaKPaths.Main.graph_estimator_machine
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T01:46:52.747519+00:00
-- url     : https://prove2.me/theorems/59e02021-fd13-41e3-bc05-5f31bddf77d8
-- title:
--   Bit-time implementation of the amplified directed-walk estimator
-- statement:
--   There is one finite-alphabet fair-bit machine $M$ and fixed natural constants $K,c$ with the following deterministic specification. For every simple directed graph, every $k\ge1$ and discrete controls $a,b\ge1$, let $L$ be the graph encoding length and put
--
--   $$B=K2^k(1+k+n+L)^c4^a(b+1).$$
--
--   The fixed sign-prefix length $S$ above is at most $B$. For every finite tape of length greater than $B$, the machine on the graph input, $k,a,b$ halts within $B$ bit steps, uses at most $B$ random bits, and writes exactly the specified amplified-estimator fraction computed from that tape prefix. The empty graph writes $0/1$.
--
--   This is the operational implementation obligation in the directed-path theorem. It asserts exact agreement with the determinant-sketch estimator, not an input oracle for a count or an estimate. The statistical accuracy theorem is separate. All constants and the finite machine are chosen before every input and every tape.
-- source:
--   Tomohiro Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, printed pp. 8–9 / PDF pp. 9–10, Section 3.2 (sampling the estimator, integer-size bound and amplification), and Section 4.1 (directed walks). Explicit fair-bit refinement uses the mission computation model in Definitions.Def_HypergraphUnreliability_FPRAS_Machine and the declared timeBudget in Definitions.Def_KoanaKPaths_Main_Inputs. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf

import Definitions.Def_KoanaKPaths_TapeSampling
open HypergraphUnreliability.FPRAS KoanaKPaths.Main

theorem KoanaKPaths.Main.graph_estimator_machine :
    ∃ (M : CoinMachine) (K c : ℕ), ∀ (n : ℕ) (arcs : List (Fin n × Fin n)),
      arcs.Nodup → (∀ p ∈ arcs, p.1 ≠ p.2) → ∀ k : ℕ, 1 ≤ k →
      ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      sampleBits n k a b ≤ timeBudget K c k (n+(graphCode n arcs).length) a b ∧
      ∀ tape : List Bool, timeBudget K c k (n+(graphCode n arcs).length) a b < tape.length →
        M.RunsWithin (graphInputControls n arcs k a b) tape
          (timeBudget K c k (n+(graphCode n arcs).length) a b)
          (fracCode (tapeEstimate n arcs k a b tape)) := by sorry
