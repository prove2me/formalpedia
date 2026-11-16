-- Prove2me | Theorems.Thm_HindsightGain_Uniform_Supplement_lemma_5_1
-- name    : HindsightGain.Uniform.Supplement.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:01:25.636456+00:00
-- url     : https://prove2.me/theorems/8ac22277-60fb-4c15-8b9a-1d6747f53ea9
-- title:
--   Lemma 5.1 — Sampling-sensitive variance bound (33) and its sharper $r=2$ form (34)
-- statement:
--   Fix $r\ge2$. Let $w_e\ge0$ for the $r$-element sets $e\subseteq[n]$, put $Q=\sum_ew_e^2$, and let $f:2^{[n]}\to\mathbb R$ satisfy
--   $$|f(U\cup\{i\})-f(U)|\le\sum_{e\ni i,\ e\setminus\{i\}\subseteq U}w_e\qquad(U\subseteq[n],\ i\notin U).\tag{32}$$
--   Then for every $p\in[0,1]$,
--   $$\mathrm{Var}\,f(S_p)\le r(1-p)p^r(1+pn)^{r-1}Q,\tag{33}$$
--   and for $r=2$ the sharper bound
--   $$\mathrm{Var}\,f(S_p)\le2p^2(1-p)^2Q+2p^3(1-p)(n-1)Q\tag{34}$$
--   also holds.
--
--   Adding or removing a variable is charged only for the interactions whose other variables are already sampled, which puts the variance on the scale of the squared bias.
--
--   Differences from the source:
--   - encoding: probability and expectation over the random retained set → exact finite sums over all subsets weighted by ∏_{i∈S}p_i∏_{i∉S}(1−p_i); reason: this is the law of the random set; no instance changes
--   - encoding: r-element sets e and the standing r ≥ 2 of §5.1 → the hypothesis 2 ≤ r and weights on Edge n r; reason: §5.1 fixes r ≥ 2
-- source:
--   Xiaohui Bei, Wenhao Wu, The Optimizer's Windfall: Bounding Hindsight Gain under Random Restrictions, STOC 2027 submission #464 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/464.pdf, Lemma 5.1, p.24 (eqs. (32)-(34))

import Mathlib
import Definitions.Def_HindsightGain_Uniform_Supplement_csp

set_option autoImplicit false
open scoped BigOperators

namespace HindsightGain.Uniform.Supplement

open HindsightGain.Uniform

/-- Lemma 5.1, p.24: (33) for every `p ∈ [0,1]`, and the sharper (34) when `r = 2`. Condition (32)
charges adding `i` to `U` only with the weights of the `r`-sets `e ∋ i` with `e \ {i} ⊆ U`. -/
theorem lemma_5_1 {n r : ℕ} (hr : 2 ≤ r) (w : Edge n r → ℝ) (hw : ∀ e, 0 ≤ w e)
    (f : Finset (Fin n) → ℝ)
    (hf : ∀ (U : Finset (Fin n)) (i : Fin n), i ∉ U →
      |f (insert i U) - f U| ≤
        ∑ e : Edge n r, if i ∈ e.val ∧ e.val.erase i ⊆ U then w e else 0)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    bernVar (fun _ => p) f ≤
        (r : ℝ) * (1 - p) * p ^ r * (1 + p * n) ^ (r - 1) * Qw w ∧
      (r = 2 → bernVar (fun _ => p) f ≤
        2 * p ^ 2 * (1 - p) ^ 2 * Qw w + 2 * p ^ 3 * (1 - p) * ((n : ℝ) - 1) * Qw w) := by sorry

end HindsightGain.Uniform.Supplement
