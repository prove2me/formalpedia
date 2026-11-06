-- Prove2me | Theorems.Thm_MinorityDynamics_lemma_8_3
-- name    : MinorityDynamics.lemma_8_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:17:29.58822+00:00
-- url     : https://prove2.me/theorems/403a23d9-08cc-49d0-a24b-1f1766096939
-- title:
--   Lemma 8.3 — hitting $\mathcal H$ with sources
-- statement:
--   Assume $k\ge L^{21/10}$ and $k=n^{o(1)}$ ($n,k$ odd, $n$ large), and $1\le\varrho\le\frac{\gamma}{16}\sqrt{K/L}$ with $\gamma=\frac1{9D}$. Consider the actual chain with $\varrho$ sources. There is an absolute constant $C>0$ such that for every initial state $(x,\sigma)\in\Omega_\varrho$,
--   $$\Pr_{x,\sigma}\big(\tau_{\mathcal H}>CDL\big)\le n^{-1},$$
--   where $\tau_{\mathcal H}$ is the first round at which the minority fraction lies in $\mathcal H$.
--
--   Differences from the source:
--   - encoding: under (3.1): k ≥ L^{21/10}, k = n^{o(1)}; n, k odd; for sufficiently large n (p.2) → ∃ ε > 0, ∃ N such that the claim holds for every odd n ≥ N and odd k with (ln n)^{21/10} ≤ k ≤ n^ε; reason: equivalent to the reading "for every sequence k(n) = n^{o(1)}, for all sufficiently large n" (a sequence violating the ε-form infinitely often can be built from counterexamples with k ≤ n^{1/i}); same instances
--   - encoding: Pr_x(τ_A > T) for the hitting time τ_A and a real T ≥ 0 → avoidProb P A ⌊T⌋₊ x: the probability, defined by the first-step recursion, that the chain avoids A at rounds 0, …, ⌊T⌋; reason: τ_A is an integer, so τ_A > T iff τ_A > ⌊T⌋; the recursion is the law of the chain; same instances
--   - encoding: states (x, σ) ∈ Ω_ϱ → pairs (minority count s, orientation σ ∈ Bool) with 2s < n, ϱσ ≤ s and s + ϱ(1−σ) ≤ n; reason: Lean convention; same instances
-- source:
--   Giakkoupis, Los, Sauerwald, Ziccardi, Minority Dynamics with Small Samples, manuscript (STOC 2027 submission), Lemma 8.3, p.43

import Mathlib
import Definitions.Def_MinorityDynamics_Kernel
import Definitions.Def_MinorityDynamics_Chain

set_option autoImplicit false

open Classical

namespace MinorityDynamics

/-- **Lemma 8.3 (Hitting H with sources)** (Giakkoupis, Los, Sauerwald, Ziccardi, *Minority Dynamics with Small Samples*, manuscript (STOC 2027 submission), p.43 = PDF p.45): "Assume (3.1) and
1 ≤ ϱ ≤ (γ/16)√(K/L). Consider the actual chain with ϱ sources. There is an absolute constant
C > 0 such that, for every initial state (x, σ) ∈ Ωϱ, Pr_{x,σ}(τH > CDL) ≤ n^{−1}."

Here `γ = 1/(9D)` (§8.1, (8.3), p.42), and `τ_H` is the first round at which the minority fraction is
in `H`.

**Formalization Note** `C` is absolute: chosen before `ε`, `N`, `n`, `k` and `ϱ`. `τ_H > CDL` is
`τ_H > ⌊CDL⌋`. "Under (3.1)" (`k ≥ L^{21/10}`, `k = n^{o(1)}`) together with the
standing "all of our statements hold for sufficiently large n" (p.2) is encoded as: there are
`ε > 0` and `N` such that the claim holds for all odd `n ≥ N` and odd `k` with
`(ln n)^{21/10} ≤ k ≤ n^ε`. This is equivalent to the paper's reading "for every sequence
`k = k(n) = n^{o(1)}`, for all sufficiently large n". `n` and `k` are odd (p.2). -/
theorem lemma_8_3 :
    ∃ C : ℝ, 0 < C ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Odd n → ∀ k : ℕ, Odd k →
    Real.log n ^ ((21 : ℝ) / 10) ≤ (k : ℝ) → (k : ℝ) ≤ (n : ℝ) ^ ε →
      ∀ ϱ : ℕ, 1 ≤ ϱ →
        (ϱ : ℝ) ≤ (1 / (9 * DD n k)) / 16 * Real.sqrt (KK n k / logN n) →
      ∀ st : Fin (n + 1) × Bool, st ∈ OmegaRho n ϱ →
        avoidProb (sourceKernel n k ϱ) {st' | st'.1 ∈ Hset n k} ⌊C * DD n k * logN n⌋₊ st ≤
          1 / n := by sorry

end MinorityDynamics
