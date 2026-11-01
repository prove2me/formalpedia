-- Prove2me | Theorems.Thm_MNLStability_lemma_13
-- name    : MNLStability.lemma_13
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:28:55.930993+00:00
-- url     : https://prove2.me/theorems/417ae003-c99e-414a-8909-b19795273879
-- title:
--   Lemma 13 — scaling down $w_a$ raises the expected choice ratio of product $a$
-- statement:
--   Let $\tilde w$ be $w$ with $\tilde w_a=(1-\varepsilon)w_a$, $\varepsilon\in[0,1)$. Let $S^m$ (resp. $\tilde S^m$) be the set of products in stock after customer $m$ under $w$ (resp. $\tilde w$), together with the no-purchase option, starting from the inventory vector $U$. Then
--
--   $$\mathbb E_{\tilde w}\!\left[\frac{\mathbb I[a\in\tilde S^m]}{w(\tilde S^m)}\right]\ \ge\ \mathbb E_{w}\!\left[\frac{\mathbb I[a\in S^m]}{w(S^m)}\right],$$
--
--   where both denominators use the original weights $w$, and $w(S)=w_0+\sum_{i\in S,i\ne0}w_i$.
--
--   The lemma turns the stochastic order of Lemma 12 into item 1 of Theorem 2 (Lemma 11).
--
--   Differences from the source:
--   - encoding: product 1 ("without loss of generality", p.10) → an arbitrary product a; reason: relabeling; the paper's case is a = product 1
--   - encoding: expectations of a bounded random variable → sums over all outcomes in [0, ∞]; reason: the integrand lies in [0, 1/w₀]; same values
-- source:
--   Aouad & Segev, The Stability of MNL-Based Demand under Dynamic Customer Substitution and its Algorithmic Implications, SSRN:3498325 (manuscript of 2019-12-04), Lemma 13, p.31; proof App. A.8, pp.48–49

import Mathlib
import Definitions.Def_MNLStability_demand
import Definitions.Def_MNLStability_scaleProd
import Definitions.Def_MNLStability_choiceRatio

namespace MNLStability

open scoped ENNReal

/-- **Lemma 13** (SSRN:3498325, p.31; proof App. A.8, pp.48–49). Let `w̃` be `w` with the weight of
product `a` scaled to `(1 − ε)·w_a`, `ε ∈ [0, 1)`. Let `S^m` (resp. `S̃^m`) be the set of products in
stock after customer `m` under `w` (resp. `w̃`), together with the no-purchase option. Then
`E_w̃[ I[a ∈ S̃^m] / w(S̃^m) ] ≥ E_w[ I[a ∈ S^m] / w(S^m) ]`,
with the original weights `w` in both denominators.

**Formalization Note.** The expectations are `ℝ≥0∞` sums over all outcomes of the `m`-customer
demand process; the integrand is at most `1/w₀`. -/
theorem lemma_13 {n : ℕ} (wts : Weights n) (hw : wts.Pos) (a : Fin n) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε1 : ε < 1) (U : Fin n → ℕ) (m : ℕ) :
    ∑' x, demand wts U m x * ENNReal.ofReal (choiceRatio wts U a x) ≤
      ∑' x, demand (scaleProd wts a ε) U m x * ENNReal.ofReal (choiceRatio wts U a x) := by sorry

end MNLStability
