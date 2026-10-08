-- Prove2me | Theorems.Thm_GenCMu_HeavyTraffic_proposition_2_jumps
-- name    : GenCMu.HeavyTraffic.proposition_2_jumps
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:45:32.691984+00:00
-- url     : https://prove2.me/theorems/8f080c6d-5975-4c59-b40e-87be55a075fb
-- title:
--   Proposition 2, (33)–(34) — the largest interarrival and service times up to time $n$ are $o(n^{1/2})$
-- statement:
--   Let $(Q^n)$ be a heavy-traffic sequence satisfying Assumption 1. Then for every class $k$
--   $$n^{-1/2}\max_{1\le i\le A^n_k(n)} u^n_{k,i} \to 0 \quad (33), \qquad n^{-1/2}\max_{1\le i\le S^n_k(n)} v^n_{k,i} \to 0 \quad (34).$$
--
--   No single interarrival or service time within the horizon is of the order of the diffusion scale; this is what makes the class workload proportional to the class headcount (Proposition 3).
--
--   **Formalization Note** The paper's $\sup_{1\le i\le A^n(n\cdot)}$ is a function of $t\in[0,1]$, nondecreasing in $t$; its uniform convergence to $0$ is the statement at $t = 1$. Assumption 1 includes the convergence of the trends' derivatives (see `GenCMu.HeavyTraffic.Limits`), without which (33)–(34) can fail.
-- source:
--   Van Mieghem, Dynamic Scheduling with Convex Delay Costs: The Generalized cμ Rule, Ann. Appl. Probab. 5(3) (1995), pp. 817–818, Proposition 2, (33)–(34)

import Mathlib
import Definitions.Def_GenCMu_HeavyTraffic_Model
import Definitions.Def_GenCMu_HeavyTraffic_Sequence
import Definitions.Def_GenCMu_HeavyTraffic_Limits

namespace GenCMu.HeavyTraffic

open Filter Topology Finset


/-- Proposition 2, (33)–(34) (p. 818): under Assumption 1, the largest interarrival time among the
first `Aⁿ_k(n)` class-`k` jobs and the largest service time among the first `Sⁿ_k(n)` are
`o(n^{1/2})`. -/
theorem proposition_2_jumps {d : ℕ} (H : HTSeq d) (M : Limits d) (h1 : MainConvergence H M) :
    ∀ k, ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      (∀ i ∈ Finset.Icc 1 ((H.Q n).A k n), (H.Q n).u k i ≤ ε * Real.sqrt n) ∧
      (∀ i ∈ Finset.Icc 1 ((H.Q n).S k n), (H.Q n).v k i ≤ ε * Real.sqrt n) := by sorry
end GenCMu.HeavyTraffic
