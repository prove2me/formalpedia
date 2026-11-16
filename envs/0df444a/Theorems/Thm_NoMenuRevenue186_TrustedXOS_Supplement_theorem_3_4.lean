-- Prove2me | Theorems.Thm_NoMenuRevenue186_TrustedXOS_Supplement_theorem_3_4
-- name    : NoMenuRevenue186.TrustedXOS.Supplement.theorem_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:06:28.971649+00:00
-- url     : https://prove2.me/theorems/dd8bbbe7-3cdd-4d21-8e2e-596a2de80057
-- title:
--   Theorem 3.4 — trusted seller, gross-substitutes buyers, buy-many benchmark
-- statement:
--   Fix $\delta\in(0,1/3)$ and write $\log$ for the logarithm to base $2$. There are a constant $c=c_\delta>0$ and, for every $n$, a finite distribution $\mathcal D_n$ over finite seller priors on gross-substitutes valuations (positive multiples of matroid rank functions) with the following property. For every $\alpha:\mathbb N\to\mathbb R$ with $\alpha(n)\ge1$ and $\alpha(n)=o(\log n)$ there is a threshold beyond which every deterministic ex-post IR, buyer-PIC protocol $\Pi$ for $\mathcal D_n$ satisfies
--
--   $$\mathrm{Rev}(\Pi)\ge\frac{\mathrm{Opt}_{bm,n}}{\alpha(n)}\quad\Longrightarrow\quad\mathrm{CC}(\Pi)\ge2^{c\,n^{1/3-\delta}}.$$
--
--   $\mathrm{Opt}_{bm,n}$ is the expected optimal deterministic buy-many (subadditive bundle pricing) revenue under the joint draw, as in Theorem 3.3. The protocol is not required to be buy-many. The witnesses have exact rational bundle values with $O(n)$ bits, attained benchmarks, and $\mathrm{Opt}_{bm,n}>0$ for large $n$; $c$ and $\mathcal D_n$ may depend on $\delta$ but not on $\alpha$ or $\Pi$.
--
--   This combines the two restrictions of Theorems 3.2 and 3.3: gross-substitutes buyers and the buy-many benchmark.
--
--   Differences from the source:
--   - encoding: for all sufficiently large n and fixed delta in (0,1/3), a hard distribution with O(n)-bit values; every protocol that o(log n)-approximates Opt_bm has no-menu complexity 2^{Omega_delta(n^{1/3-delta})} → for every delta in (0,1/3): one c > 0 and one family H (both depending on delta only) with attainment certificates, an existential linear bit bound and eventually positive OptBM, before every alpha >= 1 with alpha = o(log n); a threshold M depending on alpha; reason: the same convention as the published goal Theorem 3.1: values of the family for small n have no asymptotic effect, attainment makes the source maximum explicit, the bit convention is that of Section 2.1, and the positive benchmark excludes a degenerate witness
--   - encoding: gross-substitutes valuations → valuations equal to c times a matroid rank function on all n items, c > 0 (GSInstance); reason: Section 2.1 (printed p.8) fixes the class as "gross-substitutes valuations, and specifically positive multiples of matroid rank functions"; such functions are gross substitutes
-- source:
--   Aggarwal, Dang, Rubinstein, Zhao, STOC 2027 submission #186 (October 2026), printed p.12, PDF p.14, Theorem 3.4; proof printed p.21, PDF p.23

import Mathlib
import Definitions.Def_NoMenuRevenue186_TrustedXOS_Supplement_Classes

namespace NoMenuRevenue186.TrustedXOS.Supplement
open NoMenuRevenue186.TrustedXOS

/-- Theorem 3.4, printed p.12 (PDF p.14): trusted seller, gross-substitutes buyers,
    buy-many benchmark. For each fixed `δ ∈ (0,1/3)` there are `c > 0` and a hard family
    (both may depend on `δ`) before every `α = o(log n)`. -/
theorem theorem_3_4 :
    ∀ δ : ℝ, 0 < δ → δ < 1 / 3 →
    ∃ c : ℝ, 0 < c ∧ ∃ H : (n : ℕ) → Instance n,
      (∀ n, GSInstance (H n) ∧ BenchmarksAttained (H n)) ∧
      (∃ b n₀ : ℕ, ∀ n ≥ n₀, Precision (H n) (b * n) ∧ 0 < OptBM (H n)) ∧
      ∀ α : ℕ → ℝ, (∀ n, 1 ≤ α n) → LittleO α (fun n => Real.logb 2 n) →
        ∃ M : ℕ, ∀ n ≥ M, ∀ P : Protocol n,
          P.Feasible (H n) → OptBM (H n) / α n ≤ P.revenue (H n) →
            Real.rpow 2 (c * (n : ℝ) ^ ((1 : ℝ) / 3 - δ)) ≤ (P.cc : ℝ) := by sorry

end NoMenuRevenue186.TrustedXOS.Supplement
