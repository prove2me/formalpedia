-- Prove2me | Theorems.Thm_OnlineRealSampling_Exact_lemma_C_1
-- name    : OnlineRealSampling.Exact.lemma_C_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:00:05.897289+00:00
-- url     : https://prove2.me/theorems/05b41bf1-c155-4ace-9b79-9d885da46daa
-- title:
--   Lemma C.1 — comparison of $h(i,1/a_i)$ with $h(i,i)$
-- statement:
--   Let $C,k\ge1$. There is a constant $c>0$, depending only on $C$ and $k$, with the following property. Let $h:\mathbb R_{\ge0}^2\to\mathbb R_{\ge0}$ be nondecreasing in both arguments and satisfy
--   $$\frac{h(x,y)}{h(x',y')}\le C\Big(\frac{\log x\,\log y}{\log x'\,\log y'}\Big)^k\qquad(0\le x'\le x,\ 0\le y'\le y).\qquad(84)$$
--   Then every sequence $a_0,a_1,\dots\ge0$ with $\sum_ia_i=1$ satisfies
--   $$\sum_{i=0}^\infty a_ih(i,1/a_i)\le c\sum_{i=0}^\infty a_ih(i,i).\qquad(85)$$
--
--   Here $\log$ is the clamped logarithm. The lemma converts bounds in $\log(1/f(X))$ into bounds in $\log X$ (Theorem 5.9, Corollary C.2).
--
--   **Formalization Note** Both sums are taken in $[0,\infty]$, and a term with $a_i=0$ is $0$.
--
--   Differences from the source:
--   - reading: the quotient bound h(x,y)/h(x′,y′) ≤ C((log x log y)/(log x′ log y′))^k → h(x,y) ≤ C((log x log y)/(log x′ log y′))^k · h(x′,y′); reason: the quotient is 0/0 when h vanishes; the multiplicative form agrees with the quotient wherever h(x′,y′) > 0 and includes h ≡ 0 without assuming h > 0
--   - encoding: h : ℝ²_{≥0} → ℝ_{≥0}; sums of nonnegative terms → h : ℝ → ℝ → ℝ with all hypotheses on nonnegative arguments only; sums in [0, ∞]; reason: only the values on ℝ²_{≥0} are used; same instances
-- source:
--   Draper, Harris & Saad, Online Random Sampling with Real Probabilities, STOC 2027 submission #103, preprint dated 2026-11-02 (source.pdf sha256 66aeb5c181baf97cefba69aa26d29299e888a7a86c837a71af5b77d35f11c3e1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/103.pdf), Lemma C.1, PDF 20 / printed 19; proof PDF 20–21 / printed 19–20

import Mathlib
import Definitions.Def_OnlineRealSampling_Exact_Oracle

open MeasureTheory
open scoped ENNReal

namespace OnlineRealSampling.Exact

/-- Lemma C.1. Let `C, k ≥ 1`. There is `c > 0` (depending only on `C, k`) such that for every
`h : ℝ²_{≥0} → ℝ_{≥0}` nondecreasing in both arguments with
`h(x,y) ≤ C ((log x log y)/(log x' log y'))^k h(x',y')` for `0 ≤ x' ≤ x`, `0 ≤ y' ≤ y`, and every
nonnegative sequence `a` with `∑ a_i = 1`: `∑ a_i h(i, 1/a_i) ≤ c ∑ a_i h(i, i)` (sums in
`[0, ∞]`; zero-weight terms are `0`). -/
theorem lemma_C_1 (C k : ℝ) (hC : 1 ≤ C) (hk : 1 ≤ k) :
    ∃ c : ℝ, 0 < c ∧ ∀ h : ℝ → ℝ → ℝ,
      (∀ x y : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ h x y) →
      (∀ x x' y : ℝ, 0 ≤ x → x ≤ x' → 0 ≤ y → h x y ≤ h x' y) →
      (∀ x y y' : ℝ, 0 ≤ x → 0 ≤ y → y ≤ y' → h x y ≤ h x y') →
      (∀ x y x' y' : ℝ, 0 ≤ x' → x' ≤ x → 0 ≤ y' → y' ≤ y →
        h x y ≤ C * ((slog x * slog y) / (slog x' * slog y')) ^ k * h x' y') →
      ∀ a : ℕ → ℝ, (∀ i, 0 ≤ a i) → HasSum a 1 →
        ∑' i : ℕ, ENNReal.ofReal (a i * h i (1 / a i)) ≤
          ENNReal.ofReal c * ∑' i : ℕ, ENNReal.ofReal (a i * h i i) := by sorry

end OnlineRealSampling.Exact
