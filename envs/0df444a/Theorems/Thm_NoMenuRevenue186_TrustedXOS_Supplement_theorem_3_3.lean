-- Prove2me | Theorems.Thm_NoMenuRevenue186_TrustedXOS_Supplement_theorem_3_3
-- name    : NoMenuRevenue186.TrustedXOS.Supplement.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:05:41.272223+00:00
-- url     : https://prove2.me/theorems/9ed3e604-5cbb-4e6f-8357-d7c1e25b5c86
-- title:
--   Theorem 3.3 — trusted seller, XOS buyers, buy-many benchmark
-- statement:
--   Fix $\delta\in(0,1)$ and write $\log$ for the logarithm to base $2$. There are a constant $c=c_\delta>0$ and, for every $n$, a finite distribution $\mathcal D_n$ over finite seller priors on XOS valuations with the following property. For every $\alpha:\mathbb N\to\mathbb R$ with $\alpha(n)\ge1$ and $\alpha(n)=o(\log n)$ there is a threshold beyond which every deterministic ex-post IR, buyer-PIC protocol $\Pi$ for $\mathcal D_n$ satisfies
--
--   $$\mathrm{Rev}(\Pi)\ge\frac{\mathrm{Opt}_{bm,n}}{\alpha(n)}\quad\Longrightarrow\quad\mathrm{CC}(\Pi)\ge2^{c\,n^{1-\delta}}.$$
--
--   Here $\mathrm{Opt}_{bm,n}=\mathbb E_{D\sim\mathcal D_n}[\mathrm{Opt}_{bm}(D)]$, with $\mathrm{Opt}_{bm}(D)$ the maximum expected revenue of a deterministic subadditive bundle price menu for the known prior $D$. The protocol is not required to be a buy-many mechanism. The witnesses have exact rational bundle values with $O(n)$ bits, attained benchmarks, and $\mathrm{Opt}_{bm,n}>0$ for large $n$; $c$ and $\mathcal D_n$ may depend on $\delta$ but not on $\alpha$ or $\Pi$.
--
--   Against the weaker buy-many benchmark the inapproximability factor drops from $o(n)$ to $o(\log n)$, while the communication bound stays nearly exponential.
--
--   Differences from the source:
--   - encoding: for all sufficiently large n and fixed delta in (0,1), a hard distribution with O(n)-bit values; every protocol that o(log n)-approximates Opt_bm has no-menu complexity 2^{Omega_delta(n^{1-delta})} → for every delta in (0,1): one c > 0 and one family H (both depending on delta only) with attainment certificates, an existential linear bit bound and eventually positive OptBM, before every alpha >= 1 with alpha = o(log n); a threshold M depending on alpha; reason: the same convention as the published goal Theorem 3.1: values of the family for small n have no asymptotic effect, attainment makes the source maximum explicit, the bit convention is that of Section 2.1, and the positive benchmark excludes a degenerate witness
-- source:
--   Aggarwal, Dang, Rubinstein, Zhao, STOC 2027 submission #186 (October 2026), printed p.11, PDF p.13, Theorem 3.3; proof printed p.21, PDF p.23

import Mathlib
import Definitions.Def_NoMenuRevenue186_TrustedXOS_Auction

namespace NoMenuRevenue186.TrustedXOS.Supplement
open NoMenuRevenue186.TrustedXOS

/-- Theorem 3.3, printed p.11 (PDF p.13): trusted seller, XOS buyers, buy-many benchmark.
    For each fixed `δ ∈ (0,1)` there are `c > 0` and a hard family (both may depend on `δ`:
    `Ω_δ`) before every `α = o(log n)`. The protocol itself is any deterministic ex-post IR,
    buyer-PIC protocol; only the benchmark is buy-many. -/
theorem theorem_3_3 :
    ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ c : ℝ, 0 < c ∧ ∃ H : (n : ℕ) → Instance n,
      (∀ n, XOSInstance (H n) ∧ BenchmarksAttained (H n)) ∧
      (∃ b n₀ : ℕ, ∀ n ≥ n₀, Precision (H n) (b * n) ∧ 0 < OptBM (H n)) ∧
      ∀ α : ℕ → ℝ, (∀ n, 1 ≤ α n) → LittleO α (fun n => Real.logb 2 n) →
        ∃ M : ℕ, ∀ n ≥ M, ∀ P : Protocol n,
          P.Feasible (H n) → OptBM (H n) / α n ≤ P.revenue (H n) →
            Real.rpow 2 (c * (n : ℝ) ^ (1 - δ)) ≤ (P.cc : ℝ) := by sorry

end NoMenuRevenue186.TrustedXOS.Supplement
