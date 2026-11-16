-- Prove2me | Theorems.Thm_HindsightGain_Uniform_Supplement_corollary_5_2
-- name    : HindsightGain.Uniform.Supplement.corollary_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:54:17.019175+00:00
-- url     : https://prove2.me/theorems/cbddce78-c965-4c58-9b80-17835dcdb223
-- title:
--   Corollary 5.2 — Bounded alphabets: $q=\min\{n,C_rk^r\varepsilon^{-2}\}$ samples suffice
-- statement:
--   Fix $r\ge2$. There are constants $C_r,C_r'>0$ depending only on $r$ such that the following holds for every $k$, every Max-rCSP $g$ on $n\ge1$ variables whose alphabets have size at most $k$ and whose payoffs lie in $[0,1]$, and every $\varepsilon\in(0,1)$. Take
--   $$q=\min\{n,\ C_rk^r\varepsilon^{-2}\}.$$
--   With probability at least $5/6$ over $S=S_{q/n}$, the estimator $\mathsf{Est}_q$ samples at most $4q$ variables and satisfies $|\widehat{\mathrm{Opt}}-\mathrm{Opt}_g|\le\varepsilon n^r$. On every sample it reads at most $C_r'k^{r^2}\varepsilon^{-2r}$ payoff tables.
--
--   This gives the bounded-alphabet sample size behind Theorem 3.
--
--   **Formalization Note** The source's $O_r(k^{r^2}\varepsilon^{-2r})$ is written with an explicit constant $C_r'$ depending only on $r$, holding for every sample.
--
--   Differences from the source:
--   - encoding: nonempty finite alphabets A_i, and Opt_g(S) as a maximum over labelings of S → alphabets Fin k_i with k_i ≥ 1, and Opt_g(S) as the maximum over labelings of all variables of the payoff of constraints inside S; reason: every nonempty finite alphabet is in bijection with some Fin k_i, and labels outside S do not change that payoff
--   - encoding: probability and expectation over the random retained set → exact finite sums over all subsets weighted by ∏_{i∈S}p_i∏_{i∉S}(1−p_i); reason: this is the law of the random set; no instance changes
--   - encoding: a CSP on n variables → the hypothesis 1 ≤ n; reason: §2 fixes n ≥ 1
--   - encoding: O_r(k^{r²}ε^{−2r}) payoff tables → at most C'·k^{r²}·ε^{−2r} tables on every sample, with C' > 0 chosen with C_r before k, n, g, ε; reason: O_r denotes a constant depending only on r
--   - reading: a constant C_r → a constant C_r > 0; reason: q must be a sample size of at least 1 for Est_q to be defined, so the constant is positive
-- source:
--   Xiaohui Bei, Wenhao Wu, The Optimizer's Windfall: Bounding Hindsight Gain under Random Restrictions, STOC 2027 submission #464 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/464.pdf, Corollary 5.2, p.25

import Mathlib
import Definitions.Def_HindsightGain_Uniform_Supplement_csp

set_option autoImplicit false

namespace HindsightGain.Uniform.Supplement

/-- Corollary 5.2, p.25: alphabets of size at most `k`, payoffs in `[0,1]`,
`q = min{n, C_r k^r ε^{-2}}`. Both constants depend only on `r`; the table count bound is the
`O_r(k^{r²} ε^{-2r})` of the source with an explicit constant. -/
theorem corollary_5_2 (r : ℕ) (hr : 2 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∃ C' : ℝ, 0 < C' ∧
      ∀ (k n : ℕ) (g : CSP n r) (ε : ℝ), 1 ≤ n → 0 < ε → ε < 1 →
        (∀ i, g.k i ≤ k) → (∀ e a, 0 ≤ g.g e a ∧ g.g e a ≤ 1) →
        5 / 6 ≤ bernProb (fun _ : Fin n => min (n : ℝ) (C * (k : ℝ) ^ r * (ε⁻¹) ^ 2) / n)
            (fun S => (S.card : ℝ) ≤ 4 * min (n : ℝ) (C * (k : ℝ) ^ r * (ε⁻¹) ^ 2) ∧
              |estimator g (min (n : ℝ) (C * (k : ℝ) ^ r * (ε⁻¹) ^ 2)) S - opt g| ≤
                ε * (n : ℝ) ^ r) ∧
          ∀ S : Finset (Fin n),
            (tablesRead n r (min (n : ℝ) (C * (k : ℝ) ^ r * (ε⁻¹) ^ 2)) S : ℝ) ≤
              C' * (k : ℝ) ^ (r ^ 2) * (ε⁻¹) ^ (2 * r) := by sorry

end HindsightGain.Uniform.Supplement
