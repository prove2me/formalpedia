-- Prove2me | Theorems.Thm_NoMenuRevenue186_TrustedXOS_observation_4_4
-- name    : NoMenuRevenue186.TrustedXOS.observation_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:57:34.532216+00:00
-- url     : https://prove2.me/theorems/652dcc87-ace0-49b6-b8e7-1a418bfd76fa
-- title:
--   Observation 4.4 — supported score equals normalized payment
-- statement:
--   In the construction of Section 4.1, let $\Pi$ be a deterministic ex-post IR, buyer-PIC protocol. Consider a supported instantiation $(D_{A,u},v_{B,2^j})$ whose unique common bundle has label $u(S^*)=2^j$. If $p_j$ is the payment obtained by the prescribed strategies, then
--
--   $$\tau_j(D_{A,u},B)=p_j/2^j.$$
--
--   The score tests every simulated scale, but the incentive and IR assumptions concern only jointly supported inputs. This identity connects the truthful revenue to the planted conditional score.
--
--   Differences from the source:
--   - encoding: labels 2^j for j=0,...,K → indices j in Fin (K+1), with label computed as 2^j; reason: the index of the common label is a.2 S; every scale and every supported pair is retained
--   - generalization: Section 4.1 starts with a family supplied by Lemma 4.1, whose existence assumptions include epsilon*k >= 2 and k <= epsilon*n/8 → any exact-k separated family satisfying Construction.Valid, without the two existence inequalities; reason: the benchmark, score, and reduction arguments use the supplied family only through separation and the stated size and divisibility conditions; every trimmed source family satisfies these conditions
-- source:
--   Aggarwal, Dang, Rubinstein, Zhao, STOC 2027 submission #186 (October 2026), printed p.17, PDF p.19, Observation 4.4, Section 4.3

import Mathlib
import Definitions.Def_NoMenuRevenue186_TrustedXOS_Scores

namespace NoMenuRevenue186.TrustedXOS

/-- Observation 4.4, printed p.17 (PDF p.19). Incentives are assumed only
    on the genuine joint support, not on every simulated scale. -/
theorem observation_4_4 {n : ℕ} (C : Construction n) (hC : C.Valid)
    (P : Protocol n) (hP : P.Feasible C.instanceLaw)
    (a : C.Seed) (B : Finset (Bundle n)) (S : Bundle n) (h : C.Supported a B S) :
    C.score P a B (a.2 S) =
      (C.simulated P a B (a.2 S)).payment / (2 : ℝ) ^ (a.2 S).val := by sorry

end NoMenuRevenue186.TrustedXOS
