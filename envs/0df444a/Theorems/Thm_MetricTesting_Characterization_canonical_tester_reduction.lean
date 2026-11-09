-- Prove2me | Theorems.Thm_MetricTesting_Characterization_canonical_tester_reduction
-- name    : MetricTesting.Characterization.canonical_tester_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:37:45.488105+00:00
-- url     : https://prove2.me/theorems/29abc0b1-f47c-4a90-a4a3-31df67967309
-- title:
--   Lemma 3.2 — Canonical tester reduction
-- statement:
--   Fix the standing local matrix framework with nonempty valid targets at every order at least $k$. Assume extendability. Let $A$ be a one-sided $q$-query $\epsilon$-tester, with $\epsilon>0$, and put $r=\max\{k,2q\}$. For $n\ge r$ and any input $D$, symmetrize $A$ by an independent uniform permutation. Let $C$ read a uniform $r$-set $U$ completely and lazily simulate $A$ on the cached entries. Then
--   $$\Pr[C\text{ rejects }D]=\Pr[A^{\mathrm{sym}}\text{ rejects }D]\le\Pr_U[D[U]\notin\mathcal P_r].$$
--   The simulated tester's decision is the original tester's decision, whereas the event on the right tests local validity directly. This comparison is the reduction from general adaptive testers to sampled induced submatrices.
--
--   Differences from the source:
--   - encoding: matrices on [n] with off-diagonal values in Λ and zero diagonal → functions from two-element subsets of Fin n to the subtype Λ of nonnegative reals; reason: this is a bijective encoding of all source matrices; relabelling uses injections and no metric axiom is imposed
--   - encoding: randomized adaptive decision trees with exact real answers → measurable seed-and-history rules and absorbing-stop recursive transcripts; reason: the seed is input independent, queries may repeat, all positive matrix orders are allowed, and no computability or precision condition is added
--   - encoding: a uniform r-set and successive uniform unused images → a uniform injection Fin r into Fin n, used in first-touch order; reason: each r-set has exactly r! enumerations; revealing their positions sequentially gives precisely the source conditional sampling law
-- source:
--   Zihan Tan, Theo Teske, STOC 2027 submission #385 (October 2026), p. 9, Lemma 3.2 (PDF p. 10)

import Definitions.Def_MetricTesting_Characterization_sampling

set_option autoImplicit false

noncomputable section

namespace MetricTesting.Characterization

/-- Lemma 3.2, printed p.9 / PDF p.10. C's rejection follows the
lazy simulation, not the local-membership decision of Theorem 3.4. -/
theorem canonical_tester_reduction (F : LocalData) (hP : TargetsNonempty F)
    (hext : Extendable F) (ε : ℝ) (hε : 0 < ε) (q n : ℕ)
    (hn : max F.k (2*q) ≤ n) (A : RandomTree F.values n)
    (hA : IsTester F ε q A) (D : Array F.values n) :
    simulatedRejection F A q (max F.k (2*q)) D = symmetrizedRejection F A q D ∧
    symmetrizedRejection F A q D ≤ submatrixRejection F (max F.k (2*q)) D := by sorry

end MetricTesting.Characterization
