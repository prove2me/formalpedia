-- Prove2me | Theorems.Thm_NoMenuRevenue186_TrustedXOS_lemma_4_5
-- name    : NoMenuRevenue186.TrustedXOS.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:57:58.076774+00:00
-- url     : https://prove2.me/theorems/582d32c4-10ce-4489-8aaa-d943bc1edcce
-- title:
--   Lemma 4.5 — pointwise budget over all tested scales
-- statement:
--   Fix the Section 4.1 construction and a deterministic ex-post IR, buyer-PIC protocol $\Pi$. For every balanced seller seed $(A,u)$ and every collection $B\subseteq\mathcal F$ of size $R$, including unsupported pairs and disjoint $A,B$, the tested scores satisfy
--
--   $$\sum_{j=0}^{K}\tau_j(D_{A,u},B)\le2.$$
--
--   No assumption is made that the simulated outcomes at every scale satisfy IR or IC. Those comparisons are checked inside each score. The bound is pointwise under one fixed input tuple and does not bound the sum of expectations under the different planted laws $\pi_j$.
--
--   Differences from the source:
--   - encoding: sum over j=0,...,K → sum over Fin (K+1); reason: the finite indexing is a bijection and includes both endpoints
--   - generalization: Section 4.1 starts with a family supplied by Lemma 4.1, whose existence assumptions include epsilon*k >= 2 and k <= epsilon*n/8 → any exact-k separated family satisfying Construction.Valid, without the two existence inequalities; reason: the benchmark, score, and reduction arguments use the supplied family only through separation and the stated size and divisibility conditions; every trimmed source family satisfies these conditions
-- source:
--   Aggarwal, Dang, Rubinstein, Zhao, STOC 2027 submission #186 (October 2026), printed p.17, PDF p.19, Lemma 4.5, Section 4.3

import Mathlib
import Definitions.Def_NoMenuRevenue186_TrustedXOS_Scores

namespace NoMenuRevenue186.TrustedXOS

/-- Lemma 4.5, printed p.17 (PDF p.19). B need not intersect A, and no
    global incentive assumption is substituted for the score's actual tests. -/
theorem lemma_4_5 {n : ℕ} (C : Construction n) (hC : C.Valid)
    (P : Protocol n) (hP : P.Feasible C.instanceLaw)
    (a : C.Seed) (ha : a ∈ C.seeds) (B : Finset (Bundle n))
    (hB : B ⊆ C.F) (hcard : B.card = C.R) :
    (∑ j : Fin (C.K + 1), C.score P a B j) ≤ 2 := by sorry

end NoMenuRevenue186.TrustedXOS
