-- Prove2me | Theorems.Thm_NoMenuRevenue186_TrustedXOS_Supplement_theorem_3_5
-- name    : NoMenuRevenue186.TrustedXOS.Supplement.theorem_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:08:43.136211+00:00
-- url     : https://prove2.me/theorems/40a988a3-4f42-4159-9b60-8ddc05e9deb8
-- title:
--   Theorem 3.5 — strategic seller, additive buyers
-- statement:
--   Write $\log$ for the logarithm to base $2$. There are a constant $c>0$ and, for every $n$, a publicly known finite distribution $\mathcal D_n$ over finite-precision seller priors (rational probabilities) on additive valuations with the following property. For every $\alpha:\mathbb N\to\mathbb R$ with $\alpha(n)\ge1$ and $\alpha(n)=o(n/\log n)$ there is a threshold beyond which every deterministic ex-post IR, buyer-PIC, seller-BIC protocol $\Pi$ for $\mathcal D_n$ satisfies
--
--   $$\mathrm{Rev}(\Pi)\ge\frac{\mathrm{Opt}_n}{\alpha(n)}\quad\Longrightarrow\quad\mathrm{CC}(\Pi)\ge2^{cn}.$$
--
--   Seller-BIC (eq. (2.1)) requires, for every prior $D$ in the support of $\mathcal D_n$ and every complete seller strategy $s$ on the protocol tree, $\mathbb E_{v\sim D}[p(s,b_v)]\le\mathbb E_{v\sim D}[p(s_D,b_v)]$. The benchmark $\mathrm{Opt}_n=\mathbb E_{D\sim\mathcal D_n}[\mathrm{Opt}(D)]$ is the same as in Theorem 3.1 and carries no seller-BIC constraint. The witnesses have exact rational bundle values with $O(n)$ bits, attained benchmarks, and $\mathrm{Opt}_n>0$ for large $n$; $c$ and $\mathcal D_n$ do not depend on $\alpha$ or $\Pi$.
--
--   When the seller is strategic, exponential communication is needed even for additive buyers, whose optimal mechanisms are otherwise the simplest case.
--
--   Differences from the source:
--   - encoding: for all sufficiently large n, a hard distribution with O(n)-bit values; every protocol that o(n/log n)-approximates the benchmark has no-menu complexity 2^{Omega(n)} → a family H n for all n with maximum-attainment certificates, an existential linear bit bound and eventually positive benchmark; one c > 0 and H before every alpha >= 1 with alpha = o(g) (LittleO), and a threshold M depending on alpha; reason: the same convention as the published goal Theorem 3.1: values of the family for small n have no asymptotic effect, attainment makes the source maximum explicit, the bit convention is that of Section 2.1, and the positive benchmark excludes a degenerate witness
--   - encoding: the publicly known class supp(D) is finite and consists of finite-precision priors (Section 2.2) → H n is a FiniteLaw of FiniteLaws and FinitePrecisionPriors (H n): every prior gives rational mass to each supported valuation; reason: the standing assumption of the strategic-seller setting, stated as a property of the witness
-- source:
--   Aggarwal, Dang, Rubinstein, Zhao, STOC 2027 submission #186 (October 2026), printed p.12, PDF p.14, Theorem 3.5; setting Section 2.2, printed p.10, PDF p.12; proof Section 5, printed pp.22–32, PDF pp.24–34

import Mathlib
import Definitions.Def_NoMenuRevenue186_TrustedXOS_Supplement_Classes

namespace NoMenuRevenue186.TrustedXOS.Supplement
open NoMenuRevenue186.TrustedXOS

/-- Theorem 3.5, printed p.12 (PDF p.14): strategic seller, additive buyers. The public
    class `supp 𝒟` is finite (a `FiniteLaw`) and consists of finite-precision priors.
    One universal `c > 0` and one hard family before every `α = o(n/log n)`. -/
theorem theorem_3_5 :
    ∃ c : ℝ, 0 < c ∧ ∃ H : (n : ℕ) → Instance n,
      (∀ n, AdditiveInstance (H n) ∧ FinitePrecisionPriors (H n) ∧
        BenchmarksAttained (H n)) ∧
      (∃ b n₀ : ℕ, ∀ n ≥ n₀, Precision (H n) (b * n) ∧ 0 < Opt (H n)) ∧
      ∀ α : ℕ → ℝ, (∀ n, 1 ≤ α n) → LittleO α (fun n => (n : ℝ) / Real.logb 2 n) →
        ∃ M : ℕ, ∀ n ≥ M, ∀ P : Protocol n,
          P.Feasible (H n) → SellerBIC P (H n) → Opt (H n) / α n ≤ P.revenue (H n) →
            Real.rpow 2 (c * (n : ℝ)) ≤ (P.cc : ℝ) := by sorry

end NoMenuRevenue186.TrustedXOS.Supplement
