-- Prove2me | Theorems.Thm_GenCMu_HeavyTraffic_proposition_2_bounds
-- name    : GenCMu.HeavyTraffic.proposition_2_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:45:35.902993+00:00
-- url     : https://prove2.me/theorems/f0e62efb-ea76-4aed-83cc-01e238bf6508
-- title:
--   Proposition 2 — $\limsup_n\|\tilde N^n\|$, $\limsup_n\|\tilde T^n\|$, $\limsup_n\|\tilde W^n\|$, $\limsup_n\|\tilde\tau^n\|$ are bounded
-- statement:
--   Let $(Q^n)$ be a heavy-traffic sequence satisfying Assumption 1 and let $T^n$ be feasible work-conserving policies. There is a constant $B$ such that, for all large $n$,
--   $$|\tilde N^n_k(t)| \le B, \qquad |\tilde T^n_k(t)| \le B, \qquad |\tilde W^n_k(t)| \le B \qquad (t \in [0,1],\ 1\le k\le d),$$
--   and $|\tilde\tau^n_k(t)| \le B$ for all $t \in [0,1]$ and all large $n$.
--
--   Under any work-conserving policy, headcounts, workloads, allocation fluctuations and delays are of the diffusion order $n^{1/2}$.
--
--   **Formalization Note** The paper states the four bounds on $[0,1]$. The explicit post-horizon allocation condition cover the delay of a job arriving at the horizon.
--
--   The added `PostHorizonRegular` hypothesis requires $T^n_k(n+s\sqrt n)-T^n_k(n)=\rho_k(1)s\sqrt n+o(\sqrt n)$ uniformly for bounded $s\ge0$. It supplies the service behavior that the paper leaves unspecified after $n$.
-- source:
--   Van Mieghem, Dynamic Scheduling with Convex Delay Costs: The Generalized cμ Rule, Ann. Appl. Probab. 5(3) (1995), p. 818, Proposition 2, last clause

import Mathlib
import Definitions.Def_GenCMu_HeavyTraffic_Model
import Definitions.Def_GenCMu_HeavyTraffic_Sequence
import Definitions.Def_GenCMu_HeavyTraffic_Limits

namespace GenCMu.HeavyTraffic

open Filter Topology Finset


/-- Proposition 2, last clause (p. 818): the four scaled process norms are eventually bounded
uniformly on `[0,1]`. -/
theorem proposition_2_bounds {d : ℕ} (H : HTSeq d) (M : Limits d) (h1 : MainConvergence H M) (T : ℕ → Alloc d) (hT : ∀ n, (H.Q n).IsFeasible (T n)) (hpost : PostHorizonRegular H M T) :
    ∃ B : ℝ, ∀ᶠ n : ℕ in atTop, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ k,
      |H.Nt T n t k| ≤ B ∧ |H.Ttil T n t k| ≤ B ∧
      |H.Wt T n t k| ≤ B ∧ |H.taut T n t k| ≤ B := by sorry
end GenCMu.HeavyTraffic
