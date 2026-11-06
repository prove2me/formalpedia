-- Prove2me | Theorems.Thm_MinorityDynamics_lemma_7_1
-- name    : MinorityDynamics.lemma_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:16:54.323825+00:00
-- url     : https://prove2.me/theorems/3b097073-34ea-4a83-a45d-1fa766631f4e
-- title:
--   Lemma 7.1 — the residue condition gives $[\frac1{2n},\frac{2K}n]\subseteq\ell^{d-1}(I_*)$ with $d-1=\lfloor D\rfloor\ge1$
-- statement:
--   Assume (1.1): $k\ge L^{21/10}$, $k=n^{o(1)}$ and $2\ln n\le k^d/n\le\frac15(\ln n)^{21/20}$ ($n,k$ odd, $n$ large). Then $d-1=\lfloor D\rfloor\ge1$ and
--   $$\Big[\frac1{2n},\frac{2K}{n}\Big]\subseteq\ell^{\,d-1}(I_*),$$
--   where $\ell(y)=1-(1-y)^{1/k}$ is the inverse lower branch, $\ell^{d-1}$ its $(d-1)$-fold iterate, $I_*=[b,c]$ and $D=L/\ln k$.
--
--   So every small state lies on a lower-branch trajectory that reaches the central interval after exactly $d-1$ steps.
--
--   Differences from the source:
--   - encoding: under (1.1): k ≥ L^{21/10}, k = n^{o(1)}, 2 ln n ≤ k^d/n ≤ (1/5)(ln n)^{21/20} for some d ∈ ℕ; n, k odd; for sufficiently large n (p.2) → ∃ ε > 0, ∃ N such that the claim holds for every odd n ≥ N, odd k and d ∈ ℕ with (ln n)^{21/10} ≤ k ≤ n^ε and 2 ln n ≤ k^d/n ≤ (1/5)(ln n)^{21/20} (real quotient); reason: equivalent to the sequence reading of k = n^{o(1)} for all sufficiently large n; "for some d" in a hypothesis is "for every d" satisfying it; same instances
--   - encoding: i = d − 1 = ⌊D⌋ ≥ 1 → d = ⌊D⌋₊ + 1 ∧ 1 ≤ ⌊D⌋₊ (natural floor; D > 0); reason: same statement without natural-number subtraction
-- source:
--   Giakkoupis, Los, Sauerwald, Ziccardi, Minority Dynamics with Small Samples, manuscript (STOC 2027 submission), Lemma 7.1, p.36, (7.1)–(7.2)

import Mathlib
import Definitions.Def_MinorityDynamics_Chain

set_option autoImplicit false

open Classical

namespace MinorityDynamics

/-- **Lemma 7.1 (Implication of the residue condition)** (Giakkoupis, Los, Sauerwald, Ziccardi, *Minority Dynamics with Small Samples*, manuscript (STOC 2027 submission), p.36 = PDF p.38): "Assume
(1.1). Then (7.2) holds with i = d−1 = ⌊D⌋ ≥ 1, namely [1/(2n), 2K/n] ⊆ ℓ^{d−1}(I∗)."

All three clauses: `d − 1 = ⌊D⌋` (equivalently `d = ⌊D⌋ + 1`, (7.1)), `⌊D⌋ ≥ 1`, and the inclusion
of `[1/(2n), 2K/n]` in the image of `I∗ = [b, c]` under the `(d − 1)`-fold iterate of the inverse
lower branch `ℓ(y) = 1 − (1 − y)^{1/k}`.

**Formalization Note** "Assume (1.1)" (`k ≥ L^{21/10}`, `k = n^{o(1)}`, `2 ln n ≤ k^d/n ≤ (1/5)(ln n)^{21/20}` for some `d ∈ ℕ`, with a real quotient `k^d/n`) together with the
standing "all of our statements hold for sufficiently large n" (p.2) is encoded as: there are
`ε > 0` and `N` such that the claim holds for all odd `n ≥ N` and odd `k` with
`(ln n)^{21/10} ≤ k ≤ n^ε` and every `d` satisfying the residue condition. This is equivalent to the paper's reading "for every sequence
`k = k(n) = n^{o(1)}`, for all sufficiently large n". `n` and `k` are odd (p.2). -/
theorem lemma_7_1 :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Odd n → ∀ k : ℕ, Odd k → ∀ d : ℕ,
    Real.log n ^ ((21 : ℝ) / 10) ≤ (k : ℝ) → (k : ℝ) ≤ (n : ℝ) ^ ε →
    2 * Real.log n ≤ (k : ℝ) ^ d / n → (k : ℝ) ^ d / n ≤ (1 / 5) * Real.log n ^ ((21 : ℝ) / 20) →
      d = ⌊DD n k⌋₊ + 1 ∧ 1 ≤ ⌊DD n k⌋₊ ∧
        Set.Icc (1 / (2 * (n : ℝ))) (2 * KK n k / n) ⊆ (ell k)^[d - 1] '' Istar n k := by sorry

end MinorityDynamics
