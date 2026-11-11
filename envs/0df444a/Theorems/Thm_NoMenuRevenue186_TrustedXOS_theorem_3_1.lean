-- Prove2me | Theorems.Thm_NoMenuRevenue186_TrustedXOS_theorem_3_1
-- name    : NoMenuRevenue186.TrustedXOS.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:56:03.334368+00:00
-- url     : https://prove2.me/theorems/af9abd74-1b31-4f73-b80b-84443af4a568
-- title:
--   Theorem 3.1 — trusted-seller XOS exponential communication lower bound
-- statement:
--   There is a universal constant $c>0$ and a family of finite distributions $\mathcal D_n$ over finite seller priors on normalized monotone XOS valuations of $n$ items with the following property. For every approximation-factor function $\alpha:\mathbb N\to\mathbb R$ satisfying $\alpha(n)\ge1$ and $\alpha(n)/n\to0$, there is a threshold after which every deterministic ex-post IR, buyer-PIC protocol $\Pi$ for $\mathcal D_n$ satisfies
--
--   $$\mathrm{Rev}(\Pi)\ge\frac{\mathrm{Opt}_n}{\alpha(n)}
--   \quad\Longrightarrow\quad
--   \mathrm{CC}(\Pi)\ge2^{cn},\qquad
--   \mathrm{Opt}_n=\mathbb E_{D\sim\mathcal D_n}[\mathrm{Opt}(D)].$$
--
--   For each actual prior $D$, $\mathrm{Opt}(D)$ is the maximum revenue over unrestricted deterministic buyer-IC, ex-post IR mechanisms with nonnegative payments. The maximum is computed before averaging over $D$. The family and $c$ are independent of $\alpha$ and $\Pi$; the threshold may depend on $\alpha$. Supported valuations have exact rational bundle values of $O(n)$ bits and the benchmark is positive for sufficiently large $n$.
--
--   The seller is trusted and observes only $D$, while the buyer observes only $v$. Buyer-PIC compares against all complete adaptive buyer strategies on each jointly supported pair. Communication is the maximum depth of the public tree across every path. Leaf payments remain arbitrary nonnegative real numbers. This is the full deterministic lower bound, not an assumption of a hard score gap.
--
--   Differences from the source:
--   - encoding: for sufficiently large n, hard distributions with O(n)-bit values and maximum benchmarks → a family for all n, maximum-attainment certificates, an existential linear bit bound, eventual positive Opt, and a universal c before every sublinear alpha; reason: arbitrary initial values of the family have no asymptotic effect; attainment makes the source maximum explicit, positivity follows from the hard construction, and the bit convention comes from Section 2.1
-- source:
--   Aggarwal, Dang, Rubinstein, Zhao, STOC 2027 submission #186 (October 2026), printed p.11, PDF p.13, Theorem 3.1; standing conventions in Sections 2.1–2.3 and scopes in Section 4.6

import Mathlib
import Definitions.Def_NoMenuRevenue186_TrustedXOS_Auction

namespace NoMenuRevenue186.TrustedXOS

/-- Theorem 3.1, printed p.11 (PDF p.13), with the uniform asymptotic
    scopes of Section 4.6. No lower bound or score gap is assumed.
    Maximum attainment is explicit, so the benchmark cannot be a default sSup.
    Precision is the O(n)-bit rational convention of Section 2.1. -/
theorem theorem_3_1 :
    ∃ c : ℝ, 0 < c ∧ ∃ H : (n : ℕ) → Instance n,
      (∀ n, XOSInstance (H n) ∧ BenchmarksAttained (H n)) ∧
      (∃ b n₀ : ℕ, ∀ n ≥ n₀, Precision (H n) (b * n) ∧ 0 < Opt (H n)) ∧
      ∀ α : ℕ → ℝ, (∀ n, 1 ≤ α n) → LittleO α (fun n => (n : ℝ)) →
        ∃ M : ℕ, ∀ n ≥ M, ∀ P : Protocol n,
          P.Feasible (H n) → Opt (H n) / α n ≤ P.revenue (H n) →
            Real.rpow 2 (c * (n : ℝ)) ≤ (P.cc : ℝ) := by sorry

end NoMenuRevenue186.TrustedXOS
