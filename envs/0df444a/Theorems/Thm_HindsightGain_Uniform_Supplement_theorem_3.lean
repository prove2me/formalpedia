-- Prove2me | Theorems.Thm_HindsightGain_Uniform_Supplement_theorem_3
-- name    : HindsightGain.Uniform.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:54:51.509322+00:00
-- url     : https://prove2.me/theorems/c037a2ce-540d-442d-97f5-986d2ef77a85
-- title:
--   Theorem 3 — Sampling dense Max-rCSPs with $O(\varepsilon^{-2})$ Bernoulli samples
-- statement:
--   Fix $r\ge2$ and a bound $k$ on the alphabet sizes. There is a constant $C>0$ (depending on $r$ and $k$) such that the following holds. Let $g$ be a Max-rCSP on $n\ge1$ variables with alphabets of size at most $k$ and payoffs in $[0,1]$, and let $\varepsilon\in(0,1)$. If $S$ retains each variable independently with probability $p=\min\{1,C\varepsilon^{-2}/n\}$, then with probability at least $2/3$,
--   $$|S|\le4C\varepsilon^{-2}\qquad\text{and}\qquad\big|p^{-r}\mathrm{Opt}_g(S)-\mathrm{Opt}_g\big|\le\varepsilon n^r .$$
--
--   This is the dense Max-rCSP sampling application, improving the $O(\varepsilon^{-4})$ bound of earlier work.
--
--   Differences from the source:
--   - encoding: nonempty finite alphabets A_i, and Opt_g(S) as a maximum over labelings of S → alphabets Fin k_i with k_i ≥ 1, and Opt_g(S) as the maximum over labelings of all variables of the payoff of constraints inside S; reason: every nonempty finite alphabet is in bijection with some Fin k_i, and labels outside S do not change that payoff
--   - encoding: probability and expectation over the random retained set → exact finite sums over all subsets weighted by ∏_{i∈S}p_i∏_{i∉S}(1−p_i); reason: this is the law of the random set; no instance changes
--   - encoding: a CSP on n variables → the hypothesis 1 ≤ n; reason: §2 fixes n ≥ 1
--   - reading: a constant C → a constant C > 0; reason: p = min{1, Cε^{−2}/n} must be a retention probability and the bound fails for p = 0, so the source's constant is positive
-- source:
--   Xiaohui Bei, Wenhao Wu, The Optimizer's Windfall: Bounding Hindsight Gain under Random Restrictions, STOC 2027 submission #464 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/464.pdf, Theorem 3, p.6; proved via Corollary 5.2, p.25

import Mathlib
import Definitions.Def_HindsightGain_Uniform_Supplement_csp

set_option autoImplicit false

namespace HindsightGain.Uniform.Supplement

/-- Theorem 3, p.6: for fixed `r ≥ 2` and alphabet-size bound `k`, a constant `C = C(r,k) > 0`;
`S` retains each variable independently with `p = min{1, C ε^{-2}/n}`, and with probability at
least `2/3` both `|S| ≤ 4Cε^{-2}` and `|p^{-r} Opt_g(S) - Opt_g| ≤ ε n^r`. -/
theorem theorem_3 (r k : ℕ) (hr : 2 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (g : CSP n r) (ε : ℝ), 1 ≤ n →
      (∀ i, g.k i ≤ k) → (∀ e a, 0 ≤ g.g e a ∧ g.g e a ≤ 1) → 0 < ε → ε < 1 →
      2 / 3 ≤ bernProb (fun _ : Fin n => min 1 (C * (ε⁻¹) ^ 2 / n)) (fun S =>
        (S.card : ℝ) ≤ 4 * C * (ε⁻¹) ^ 2 ∧
        |((min 1 (C * (ε⁻¹) ^ 2 / n)) ^ r)⁻¹ * optOn g S - opt g| ≤ ε * (n : ℝ) ^ r) := by sorry

end HindsightGain.Uniform.Supplement
