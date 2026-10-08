-- Prove2me | Theorems.Thm_GenCMu_HeavyTraffic_proposition_2_W
-- name    : GenCMu.HeavyTraffic.proposition_2_W
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:45:41.453079+00:00
-- url     : https://prove2.me/theorems/3f687cc0-a8f8-47b7-8e07-e41a65bdc251
-- title:
--   Proposition 2, (32) — the total workload converges: $\tilde W^n_+ \to \tilde W^*_+ = \varphi(\tilde L^*_+ + \tilde c^*)$
-- statement:
--   Let $(Q^n)$ be a heavy-traffic sequence satisfying Assumption 1 and let $T^n$ be feasible work-conserving policies. Then, uniformly on $[0,1]$,
--   $$\tilde W^n_+ \to \tilde W^*_+ = \varphi\big(\tilde L^*_+ + \tilde c^*\big),$$
--   where $\tilde L^*_+ = \sum_k \tilde L^*_k$ with $\tilde L^*_k = (\tilde A^*_k - \tilde S^*_k\circ R^*_k)/(\mu_k\circ R^*_k)$, $\tilde c^*$ is the heavy-traffic drift of (17), and $\varphi$ is the one-dimensional reflection map $\varphi(x)(t) = x(t) + \sup_{0\le s\le t}\max(0,-x(s))$.
--
--   The scaled total workload has the same limit under every work-conserving policy. The class workloads $\tilde W^n_k$ need not converge; how the total is split among classes is what scheduling controls.
--
--   **Formalization Note** The paper states (32) as "$\tilde W^n_+ \to \tilde W^*_+ \in \mathcal C$" and identifies the limit in the appendix, (72)–(74); we state the convergence to that explicit limit. The paper states it "for any scheduling policy"; its proof uses $W^n_+ = \varphi(X^n)$, which holds for work-conserving policies, and we state it for those.
-- source:
--   Van Mieghem, Dynamic Scheduling with Convex Delay Costs: The Generalized cμ Rule, Ann. Appl. Probab. 5(3) (1995), pp. 817–818, Proposition 2, (32); limit from Appendix, (70)–(74), p. 827

import Mathlib
import Definitions.Def_GenCMu_HeavyTraffic_Model
import Definitions.Def_GenCMu_HeavyTraffic_Sequence
import Definitions.Def_GenCMu_HeavyTraffic_Limits

namespace GenCMu.HeavyTraffic

open Filter Topology Finset


/-- Proposition 2, (32) (p. 818), with the limit identified by (70)–(74) (p. 827): for every sequence
of feasible work-conserving policies, the scaled total workload `W̃ⁿ_+` converges uniformly on
`[0, 1]` to `W̃*_+ = φ(L̃*_+ + c̃*)`. -/
theorem proposition_2_W {d : ℕ} (H : HTSeq d) (M : Limits d) (h1 : MainConvergence H M) (T : ℕ → Alloc d) (hT : ∀ n, (H.Q n).IsFeasible (T n)) :
    TendstoUniformlyOn (H.Wpt T) (Wstar M) atTop (Set.Icc 0 1) := by sorry
end GenCMu.HeavyTraffic
