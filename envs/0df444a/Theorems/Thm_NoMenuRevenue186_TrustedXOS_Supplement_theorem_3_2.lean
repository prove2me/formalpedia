-- Prove2me | Theorems.Thm_NoMenuRevenue186_TrustedXOS_Supplement_theorem_3_2
-- name    : NoMenuRevenue186.TrustedXOS.Supplement.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:04:29.349728+00:00
-- url     : https://prove2.me/theorems/ff7efa69-d5c7-4dae-9bea-ae4171bf0b6a
-- title:
--   Theorem 3.2 — trusted seller, gross-substitutes buyers
-- statement:
--   Write $\log$ for the logarithm to base $2$ and $g(n)=n^{1/3}/\log n$. There are a constant $c>0$ and, for every number of items $n$, a finite distribution $\mathcal D_n$ over finite seller priors on gross-substitutes valuations (positive multiples of matroid rank functions) with the following property. For every approximation factor $\alpha:\mathbb N\to\mathbb R$ with $\alpha(n)\ge1$ and $\alpha=o(g)$ there is a threshold beyond which every deterministic ex-post IR, buyer-PIC protocol $\Pi$ for $\mathcal D_n$ satisfies
--
--   $$\mathrm{Rev}(\Pi)\ge\frac{\mathrm{Opt}_n}{\alpha(n)}\quad\Longrightarrow\quad\mathrm{CC}(\Pi)\ge 2^{c\,n^{1/3}/\log n}.$$
--
--   Here $\mathrm{Opt}_n=\mathbb E_{D\sim\mathcal D_n}[\mathrm{Opt}(D)]$, with $\mathrm{Opt}(D)$ the maximum revenue of a deterministic buyer-IC, ex-post IR mechanism for the known prior $D$, and $\mathrm{CC}(\Pi)$ is the depth of the whole protocol tree. The witnesses also have exact rational bundle values with $O(n)$ bits, attained benchmarks, and $\mathrm{Opt}_n>0$ for large $n$; $c$ and $\mathcal D_n$ do not depend on $\alpha$ or $\Pi$.
--
--   This is the gross-substitutes companion of the mission's goal (Theorem 3.1): the same no-menu lower bound holds for a much more restricted valuation class, with a smaller exponent.
--
--   Differences from the source:
--   - encoding: for all sufficiently large n, a hard distribution with O(n)-bit values; every protocol that o(n^{1/3}/log n)-approximates the benchmark has no-menu complexity 2^{Omega(n^{1/3}/log n)} → a family H n for all n with maximum-attainment certificates, an existential linear bit bound and eventually positive benchmark; one c > 0 and H before every alpha >= 1 with alpha = o(g) (LittleO), and a threshold M depending on alpha; reason: the same convention as the published goal Theorem 3.1: values of the family for small n have no asymptotic effect, attainment makes the source maximum explicit, the bit convention is that of Section 2.1, and the positive benchmark excludes a degenerate witness
--   - encoding: gross-substitutes valuations → valuations equal to c times a matroid rank function on all n items, c > 0 (GSInstance); reason: Section 2.1 (printed p.8) fixes the class as "gross-substitutes valuations, and specifically positive multiples of matroid rank functions"; such functions are gross substitutes
-- source:
--   Aggarwal, Dang, Rubinstein, Zhao, STOC 2027 submission #186 (October 2026), printed p.11, PDF p.13, Theorem 3.2; proof printed p.20, PDF p.22

import Mathlib
import Definitions.Def_NoMenuRevenue186_TrustedXOS_Supplement_Classes

namespace NoMenuRevenue186.TrustedXOS.Supplement
open NoMenuRevenue186.TrustedXOS

/-- Theorem 3.2, printed p.11 (PDF p.13): trusted seller, gross-substitutes buyers.
    One universal `c > 0` and one hard family before every `α = o(n^{1/3}/log n)`;
    the threshold may depend on `α`. `log` is base 2 (Section 2.1). -/
theorem theorem_3_2 :
    ∃ c : ℝ, 0 < c ∧ ∃ H : (n : ℕ) → Instance n,
      (∀ n, GSInstance (H n) ∧ BenchmarksAttained (H n)) ∧
      (∃ b n₀ : ℕ, ∀ n ≥ n₀, Precision (H n) (b * n) ∧ 0 < Opt (H n)) ∧
      ∀ α : ℕ → ℝ, (∀ n, 1 ≤ α n) →
        LittleO α (fun n => (n : ℝ) ^ ((1 : ℝ) / 3) / Real.logb 2 n) →
        ∃ M : ℕ, ∀ n ≥ M, ∀ P : Protocol n,
          P.Feasible (H n) → Opt (H n) / α n ≤ P.revenue (H n) →
            Real.rpow 2 (c * ((n : ℝ) ^ ((1 : ℝ) / 3) / Real.logb 2 n)) ≤ (P.cc : ℝ) := by sorry

end NoMenuRevenue186.TrustedXOS.Supplement
