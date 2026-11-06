-- Prove2me | Theorems.Thm_MinorityDynamics_lemma_8_6
-- name    : MinorityDynamics.lemma_8_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:17:31.307013+00:00
-- url     : https://prove2.me/theorems/9c24689e-615d-45c6-88d4-3e1087fddb19
-- title:
--   Lemma 8.6 — consensus from $\mathcal H$ with sources: $\Pr(\tau_0>C_1D)\le 5n^{-1/2}$
-- statement:
--   Assume (8.3): condition (1.1) ($n,k$ odd, $n$ large) and $1\le\varrho\le\frac{\ln k}{144}\sqrt{k/L^{81/20}}$ $\big(=\frac{\gamma}{16}\sqrt{K/L}\big)$. Consider the actual chain with $\varrho$ sources. There is an absolute constant $C_1>0$ such that for every initial state $(x,\sigma)\in\Omega_\varrho$ with $x\in\mathcal H$,
--   $$\Pr_{x,\sigma}\big(\tau_0>C_1D\big)\le 5n^{-1/2},$$
--   where $\tau_0$ is the first round at which the minority fraction is $0$ (consensus, necessarily on the sources' opinion).
--
--   Differences from the source:
--   - encoding: under (1.1): k ≥ L^{21/10}, k = n^{o(1)}, 2 ln n ≤ k^d/n ≤ (1/5)(ln n)^{21/20} for some d ∈ ℕ; n, k odd; for sufficiently large n (p.2) → ∃ ε > 0, ∃ N such that the claim holds for every odd n ≥ N, odd k and d ∈ ℕ with (ln n)^{21/10} ≤ k ≤ n^ε and 2 ln n ≤ k^d/n ≤ (1/5)(ln n)^{21/20} (real quotient); reason: equivalent to the sequence reading of k = n^{o(1)} for all sufficiently large n; "for some d" in a hypothesis is "for every d" satisfying it; same instances
--   - encoding: Pr_x(τ_A > T) for the hitting time τ_A and a real T ≥ 0 → avoidProb P A ⌊T⌋₊ x: the probability, defined by the first-step recursion, that the chain avoids A at rounds 0, …, ⌊T⌋; reason: τ_A is an integer, so τ_A > T iff τ_A > ⌊T⌋; the recursion is the law of the chain; same instances
--   - encoding: states (x, σ) ∈ Ω_ϱ → pairs (minority count s, orientation σ ∈ Bool) with 2s < n, ϱσ ≤ s and s + ϱ(1−σ) ≤ n; reason: Lean convention; same instances
-- source:
--   Giakkoupis, Los, Sauerwald, Ziccardi, Minority Dynamics with Small Samples, manuscript (STOC 2027 submission), Lemma 8.6, p.47, (8.3)

import Mathlib
import Definitions.Def_MinorityDynamics_Kernel
import Definitions.Def_MinorityDynamics_Chain

set_option autoImplicit false

open Classical

namespace MinorityDynamics

/-- **Lemma 8.6 (Consensus from H with sources)** (Giakkoupis, Los, Sauerwald, Ziccardi, *Minority Dynamics with Small Samples*, manuscript (STOC 2027 submission), p.47 = PDF p.49): "Assume (8.3), and
consider the actual chain with ϱ sources. There is an absolute constant C1 > 0 such that, for every
initial state (x, σ) ∈ Ωϱ with x ∈ H, Pr_{x,σ}(τ0 > C1D) ≤ 5n^{−1/2}."

(8.3) (p.42) is (1.1) together with `1 ≤ ϱ ≤ (γ/16)√(K/L) = (ln k/144)√(k/L^{81/20})`;
`τ₀` is the first round at which the minority fraction is `0` (consensus).

**Formalization Note** `C₁` is absolute: chosen before `ε`, `N`, `n`, `k`, `d` and `ϱ`. `τ₀ > C₁D` is
`τ₀ > ⌊C₁D⌋`. The bound on `ϱ` is written in the form `(ln k/144)√(k/L^{81/20})` of (8.3).
"Assume (1.1)" (`k ≥ L^{21/10}`, `k = n^{o(1)}`, `2 ln n ≤ k^d/n ≤ (1/5)(ln n)^{21/20}` for some `d ∈ ℕ`, with a real quotient `k^d/n`) together with the
standing "all of our statements hold for sufficiently large n" (p.2) is encoded as: there are
`ε > 0` and `N` such that the claim holds for all odd `n ≥ N` and odd `k` with
`(ln n)^{21/10} ≤ k ≤ n^ε` and every `d` satisfying the residue condition. This is equivalent to the paper's reading "for every sequence
`k = k(n) = n^{o(1)}`, for all sufficiently large n". `n` and `k` are odd (p.2). -/
theorem lemma_8_6 :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Odd n → ∀ k : ℕ, Odd k →
      ∀ d : ℕ,
    Real.log n ^ ((21 : ℝ) / 10) ≤ (k : ℝ) → (k : ℝ) ≤ (n : ℝ) ^ ε →
    2 * Real.log n ≤ (k : ℝ) ^ d / n → (k : ℝ) ^ d / n ≤ (1 / 5) * Real.log n ^ ((21 : ℝ) / 20) →
      ∀ ϱ : ℕ, 1 ≤ ϱ →
        (ϱ : ℝ) ≤ Real.log k / 144 * Real.sqrt ((k : ℝ) / logN n ^ ((81 : ℝ) / 20)) →
      ∀ st : Fin (n + 1) × Bool, st ∈ OmegaRho n ϱ → st.1 ∈ Hset n k →
        avoidProb (sourceKernel n k ϱ) {st' | (st'.1 : ℕ) = 0} ⌊C₁ * DD n k⌋₊ st ≤
          5 * (n : ℝ) ^ (-(1 : ℝ) / 2) := by sorry

end MinorityDynamics
