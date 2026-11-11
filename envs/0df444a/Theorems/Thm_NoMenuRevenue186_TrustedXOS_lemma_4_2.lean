-- Prove2me | Theorems.Thm_NoMenuRevenue186_TrustedXOS_lemma_4_2
-- name    : NoMenuRevenue186.TrustedXOS.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:56:54.382222+00:00
-- url     : https://prove2.me/theorems/0a901b46-eba3-4a89-8ba1-b771678e2194
-- title:
--   Lemma 4.2 — pointwise benchmark revenue extraction
-- statement:
--   Take the almost-disjoint bundle construction with $0<\epsilon<1$, $K\ge1$, $N=4R$, and the positive divisible collection size and balanced labels of Section 4.1. There exists a deterministic protocol $\Pi$ with unrestricted communication, nonnegative real leaf payments, ex-post IR, and buyer-PIC such that every supported instantiation with unique common bundle $S^*$ has payment
--
--   $$p_\Pi(D_{A,u},v_{B,u(S^*)})=(1-\epsilon)u(S^*).$$
--
--   The tree and the strategy prescriptions can depend on the public construction. The seller prescription reads only the actual prior and the buyer prescription only the actual valuation. No upper bound on communication is required. This establishes the pointwise benchmark witness used by the lower bound.
--
--   Differences from the source:
--   - encoding: supported instantiations (D_{A,u},v_{B,u(S*)}) → balanced seeds and collections with A intersect B equal to {S*}, evaluated at actual priors and valuations; reason: these tuples parameterize exactly the joint support; strategies do not receive the seeds as extra private inputs
--   - generalization: Section 4.1 starts with a family supplied by Lemma 4.1, whose existence assumptions include epsilon*k >= 2 and k <= epsilon*n/8 → any exact-k separated family satisfying Construction.Valid, without the two existence inequalities; reason: the benchmark, score, and reduction arguments use the supplied family only through separation and the stated size and divisibility conditions; every trimmed source family satisfies these conditions
-- source:
--   Aggarwal, Dang, Rubinstein, Zhao, STOC 2027 submission #186 (October 2026), printed p.16, PDF p.18, Lemma 4.2, with the construction in Section 4.1

import Mathlib
import Definitions.Def_NoMenuRevenue186_TrustedXOS_Construction

namespace NoMenuRevenue186.TrustedXOS

/-- Lemma 4.2, printed p.16 (PDF p.18). The public tree may depend on C,
    but its seller prescription receives only the actual prior. -/
theorem lemma_4_2 {n : ℕ} (C : Construction n) (hC : C.Valid) :
    ∃ P : Protocol n, P.Feasible C.instanceLaw ∧
      ∀ (a : C.Seed) (B : Finset (Bundle n)) (S : Bundle n), C.Supported a B S →
        (P.outcome (C.prior a) (C.value B (a.2 S))).payment =
          (1 - C.ε) * (2 : ℝ) ^ (a.2 S).val := by sorry

end NoMenuRevenue186.TrustedXOS
