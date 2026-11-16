-- Prove2me | Theorems.Thm_HindsightGain_Uniform_Supplement_theorem_10
-- name    : HindsightGain.Uniform.Supplement.theorem_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:02:03.167575+00:00
-- url     : https://prove2.me/theorems/5475cf59-5f9f-4f91-816b-1bbeead8e9ac
-- title:
--   Theorem 10 — Energy-sensitive estimator with joint success $5/6$
-- statement:
--   Fix $r\ge2$. There is a constant $C_r>0$ such that the following holds. Let $g$ be a Max-rCSP and $w$ weights with $0\le g_e\le w_e$ entrywise, and let $q$ be real with $1\le q\le n$. With probability at least $5/6$ over $S=S_{q/n}$, the estimator $\mathsf{Est}_q$ samples at most $4q$ variables and satisfies
--   $$\big|\widehat{\mathrm{Opt}}-\mathrm{Opt}_g\big|\le C_r\frac{n^{r/2}}{\sqrt q}\Big(\mathcal E(g)+\sqrt{Q(w)}\Big).$$
--
--   The actual table norms enter only through $Q(w)$, which can give a better alphabet dependence than Corollary 5.2 for sparse tables.
--
--   Differences from the source:
--   - encoding: nonempty finite alphabets A_i, and Opt_g(S) as a maximum over labelings of S → alphabets Fin k_i with k_i ≥ 1, and Opt_g(S) as the maximum over labelings of all variables of the payoff of constraints inside S; reason: every nonempty finite alphabet is in bijection with some Fin k_i, and labels outside S do not change that payoff
--   - encoding: probability and expectation over the random retained set → exact finite sums over all subsets weighted by ∏_{i∈S}p_i∏_{i∉S}(1−p_i); reason: this is the law of the random set; no instance changes
-- source:
--   Xiaohui Bei, Wenhao Wu, The Optimizer's Windfall: Bounding Hindsight Gain under Random Restrictions, STOC 2027 submission #464 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/464.pdf, Theorem 10, p.25

import Mathlib
import Definitions.Def_HindsightGain_Uniform_Supplement_csp

set_option autoImplicit false

namespace HindsightGain.Uniform.Supplement

open HindsightGain.Uniform

/-- Theorem 10, p.25: for `0 ≤ g_e ≤ w_e` and real `1 ≤ q ≤ n`, with probability at least `5/6`
over `S = S_{q/n}`, both `|S| ≤ 4q` and the accuracy bound for `Est_q` hold. -/
theorem theorem_10 (r : ℕ) (hr : 2 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (g : CSP n r) (w : Edge n r → ℝ) (q : ℝ),
      (∀ e a, 0 ≤ g.g e a ∧ g.g e a ≤ w e) → 1 ≤ q → q ≤ n →
      5 / 6 ≤ bernProb (fun _ : Fin n => q / n) (fun S =>
        (S.card : ℝ) ≤ 4 * q ∧
        |estimator g q S - opt g| ≤
          C * (n : ℝ) ^ ((r : ℝ) / 2) / Real.sqrt q * (energy g + Real.sqrt (Qw w))) := by sorry

end HindsightGain.Uniform.Supplement
