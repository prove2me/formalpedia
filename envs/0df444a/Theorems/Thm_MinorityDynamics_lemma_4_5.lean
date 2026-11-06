-- Prove2me | Theorems.Thm_MinorityDynamics_lemma_4_5
-- name    : MinorityDynamics.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:17:39.329724+00:00
-- url     : https://prove2.me/theorems/d66d0aad-ac36-4170-9a21-4d1758b18691
-- title:
--   Lemma 4.5 — weighted transition estimates (4.9)–(4.11)
-- statement:
--   Assume $k\ge L^{21/10}$ and $k=n^{o(1)}$ ($n,k$ odd, $n$ large). For every $y=s/n\in\mathcal S\cap(K/n,b)$, with $t=\ln(1/y)$ and $\delta_s=\sqrt{L\ln L/s}$,
--   $$\mathcal L(y)\le\frac{\alpha(y/k)}{\alpha(y)}+O(\delta_s+b)+\Big(\frac12+o(1)\Big)\min\Big\{\frac{k}{\sqrt s},\sqrt{\frac kK}\Big\},\qquad(4.9)$$
--   $$\mathcal R(y)\le\frac{1}{\alpha(y)t}+O\Big(\frac{\delta_s}{t^2}+k^{-1/2}+\frac{k\sqrt s}{n}\Big),\qquad(4.10)$$
--   and for every $y\in\mathcal S\cap(c,1/2)$,
--   $$\frac{(\pi Q)(y)}{\pi(y)}\le\frac78+O\Big(k^{-1/2}+\frac{k}{\sqrt n}\Big).\qquad(4.11)$$
--   All error estimates are uniform over the indicated targets: there is one absolute constant $C$ for all $O(\cdot)$ terms, and for every $\eta>0$ the $o(1)$ is at most $\eta$ once $n$ is large, simultaneously for all targets $y$.
--
--   These estimates compare the one-step weighted inflow of the stopped auxiliary chain with the continuous calculation; Lemma 4.6 is derived from them.
--
--   Differences from the source:
--   - encoding: under (3.1): k ≥ L^{21/10}, k = n^{o(1)}; n, k odd; for sufficiently large n (p.2) → ∃ ε > 0, ∃ N such that the claim holds for every odd n ≥ N and odd k with (ln n)^{21/10} ≤ k ≤ n^ε; reason: equivalent to the reading "for every sequence k(n) = n^{o(1)}, for all sufficiently large n" (a sequence violating the ε-form infinitely often can be built from counterexamples with k ≤ n^{1/i}); same instances
--   - encoding: states x ∈ Ω = {0, 1/n, …, (n−1)/(2n)} → minority counts s ∈ Fin (n+1) with 2s < n, and x = s/n; reason: Lean convention for the finite state space; same instances
--   - reading: O(·) and (1/2 + o(1)), "uniform over the indicated targets" → ∃ C > 0 (absolute, chosen first) for every O(·); ∀ η > 0 the o(1) is ≤ η, then ε and N, for all targets; reason: the stronger reading (constants independent of the sample-size sequence); the uniformity is the order of quantifiers
-- source:
--   Giakkoupis, Los, Sauerwald, Ziccardi, Minority Dynamics with Small Samples, manuscript (STOC 2027 submission), Lemma 4.5, p.19, (4.8)–(4.11)

import Mathlib
import Definitions.Def_MinorityDynamics_Chain
import Definitions.Def_MinorityDynamics_Weights

set_option autoImplicit false

open Classical

namespace MinorityDynamics

/-- **Lemma 4.5 (Weighted transition estimates)** (Giakkoupis, Los, Sauerwald, Ziccardi, *Minority Dynamics with Small Samples*, manuscript (STOC 2027 submission), p.19 = PDF p.21), under (3.1):
"For every y = s/n ∈ S ∩ (K/n, b), put t = ln(1/y) and define δs by (4.8). Then
𝓛(y) ≤ α(y/k)/α(y) + O(δs + b) + (1/2 + o(1)) min{k/√s, √(k/K)}, (4.9)
𝓡(y) ≤ 1/(α(y)t) + O(δs/t² + k^{−1/2} + k√s/n). (4.10)
For every y ∈ S ∩ (c, 1/2), (πQ)(y)/π(y) ≤ 7/8 + O(k^{−1/2} + k/√n). (4.11)
All error estimates are uniform over the indicated targets."

Here `δ_s = √(L ln L/s)` (4.8), `𝓛`, `𝓡` are the normalized lower- and middle/upper-branch
contributions (p.18), `π` the reference weights (Definition 4.4) and `Q` the matrix (4.1).

**Formalization Note** Every `O(·)` is `≤ C·(·)` with one absolute constant `C > 0`, chosen first;
`(1/2 + o(1))` is `(1/2 + η)` for every `η > 0`, after which `ε` and `N` are chosen; the bounds then
hold for every target, which is the stated uniformity. "Under (3.1)" (`k ≥ L^{21/10}`, `k = n^{o(1)}`) together with the
standing "all of our statements hold for sufficiently large n" (p.2) is encoded as: there are
`ε > 0` and `N` such that the claim holds for all odd `n ≥ N` and odd `k` with
`(ln n)^{21/10} ≤ k ≤ n^ε`. This is equivalent to the paper's reading "for every sequence
`k = k(n) = n^{o(1)}`, for all sufficiently large n". `n` and `k` are odd (p.2). -/
theorem lemma_4_5 :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Odd n →
      ∀ k : ℕ, Odd k →
    Real.log n ^ ((21 : ℝ) / 10) ≤ (k : ℝ) → (k : ℝ) ≤ (n : ℝ) ^ ε →
      (∀ s : Fin (n + 1), s ∈ Sset n k → KK n k / n < ((s : ℕ) : ℝ) / n →
        ((s : ℕ) : ℝ) / n < bPt n k →
        Lcontrib n k s ≤
            alphaW n k (((s : ℕ) : ℝ) / n / k) / alphaW n k (((s : ℕ) : ℝ) / n) +
              C * (deltaS n (s : ℕ) + bPt n k) +
              (1 / 2 + η) * min ((k : ℝ) / Real.sqrt (s : ℕ)) (Real.sqrt ((k : ℝ) / KK n k)) ∧
          Rcontrib n k s ≤
            1 / (alphaW n k (((s : ℕ) : ℝ) / n) * Real.log (1 / (((s : ℕ) : ℝ) / n))) +
              C * (deltaS n (s : ℕ) / Real.log (1 / (((s : ℕ) : ℝ) / n)) ^ 2 +
                1 / Real.sqrt k + (k : ℝ) * Real.sqrt (s : ℕ) / n)) ∧
      (∀ s : Fin (n + 1), s ∈ Sset n k → cPt n k < ((s : ℕ) : ℝ) / n →
        ((s : ℕ) : ℝ) / n < 1 / 2 →
        piQ n k s / piRef n k (((s : ℕ) : ℝ) / n) ≤
          7 / 8 + C * (1 / Real.sqrt k + (k : ℝ) / Real.sqrt n)) := by sorry

end MinorityDynamics
