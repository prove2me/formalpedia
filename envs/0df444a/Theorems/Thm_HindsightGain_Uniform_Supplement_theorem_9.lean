-- Prove2me | Theorems.Thm_HindsightGain_Uniform_Supplement_theorem_9
-- name    : HindsightGain.Uniform.Supplement.theorem_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:00:56.720843+00:00
-- url     : https://prove2.me/theorems/9a552dce-a820-4698-b6bf-90267dde4668
-- title:
--   Theorem 9 — Hindsight gain for Max-rCSPs, nonuniform (30) and uniform (31)
-- statement:
--   Fix $r\ge2$. There is a constant $C_r>0$, independent of the number of variables, the alphabets and the payoffs, such that for every Max-rCSP $g$ with arbitrary real payoff tables:
--   1. if $S$ contains each variable $i$ independently with probability $p_i\in[0,1]$, then
--   $$0\le\mathbb E\,\mathrm{Opt}_g(S)-\mathrm{Opt}_{g,p}\le C_r\,\mathcal E(g)\Big(\sum_ip_i\Big)^{(r-1)/2}\sqrt{\max_ip_i(1-p_i)};\tag{30}$$
--   2. for uniform retention with probability $p\in(0,1]$,
--   $$0\le\mathbb E\,\mathrm{Opt}_g(S_p)-p^r\mathrm{Opt}_g\le C_r\,p^{r-1/2}\sqrt{1-p}\,n^{(r-1)/2}\,\mathcal E(g).\tag{31}$$
--
--   Here $\mathcal E(g)$ is the centered energy, each table centered by its own average. These bounds control the bias of the sample-and-solve estimator.
--
--   Differences from the source:
--   - encoding: nonempty finite alphabets A_i, and Opt_g(S) as a maximum over labelings of S → alphabets Fin k_i with k_i ≥ 1, and Opt_g(S) as the maximum over labelings of all variables of the payoff of constraints inside S; reason: every nonempty finite alphabet is in bijection with some Fin k_i, and labels outside S do not change that payoff
--   - encoding: probability and expectation over the random retained set → exact finite sums over all subsets weighted by ∏_{i∈S}p_i∏_{i∉S}(1−p_i); reason: this is the law of the random set; no instance changes
-- source:
--   Xiaohui Bei, Wenhao Wu, The Optimizer's Windfall: Bounding Hindsight Gain under Random Restrictions, STOC 2027 submission #464 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/464.pdf, Theorem 9, p.23 (eqs. (30), (31)); centered energy (28), p.22

import Mathlib
import Definitions.Def_HindsightGain_Uniform_Supplement_csp

set_option autoImplicit false
open scoped BigOperators

namespace HindsightGain.Uniform.Supplement

/-- Theorem 9, p.23: both (30) (independent retention with arbitrary `p_i ∈ [0,1]`) and (31)
(uniform retention, `0 < p ≤ 1`), with one constant `C_r` chosen before the number of variables,
the alphabets and the (arbitrary real) payoff tables. -/
theorem theorem_9 (r : ℕ) (hr : 2 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (g : CSP n r),
      (∀ p : Fin n → ℝ, (∀ i, 0 ≤ p i ∧ p i ≤ 1) →
        0 ≤ bernExp p (optOn g) - optWeighted g p ∧
        bernExp p (optOn g) - optWeighted g p ≤
          C * energy g * (∑ i, p i) ^ (((r : ℝ) - 1) / 2) *
            Real.sqrt (⨆ i, p i * (1 - p i))) ∧
      (∀ p : ℝ, 0 < p → p ≤ 1 →
        0 ≤ bernExp (fun _ => p) (optOn g) - p ^ r * opt g ∧
        bernExp (fun _ => p) (optOn g) - p ^ r * opt g ≤
          C * p ^ ((r : ℝ) - 1 / 2) * Real.sqrt (1 - p) *
            (n : ℝ) ^ (((r : ℝ) - 1) / 2) * energy g) := by sorry

end HindsightGain.Uniform.Supplement
