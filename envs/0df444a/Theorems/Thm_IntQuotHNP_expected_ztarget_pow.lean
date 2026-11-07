-- Prove2me | Theorems.Thm_IntQuotHNP_expected_ztarget_pow
-- name    : IntQuotHNP.expected_ztarget_pow
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:54:21.560002+00:00
-- url     : https://prove2.me/theorems/bf8d09bb-4a20-4bba-ac5a-a841264afde2
-- title:
--   Proof of Theorem 4.2 — $E[Z_{\mathrm{target}}^N]-1=N\int_1^Xu^{N-1}\Pr[Z_{\mathrm{target}}>u]\,du\le NB\log X=\mathrm{poly}_{N,A}(\log p)$
-- statement:
--   For every $N\ge3$ there is a constant $C_N>0$ in (7), and for every $A\ge0$ there are $c,C,K,K',p_0$, such that for every prime $p\ge p_0$, every integer $1\le X<p$ with $X\le p^{\xi_N}(\log p)^A$ and every secret $y^*\in\mathbb Z_p$, under the sampling rule and with $B=c(\log p)^K$,
--   $$
--   E[Z_{\mathrm{target}}^N]-1=N\int_1^Xu^{N-1}\Pr[Z_{\mathrm{target}}>u]\,du\le N\int_1^Xu^{N-1}\Psi_X(u)\,du\le NB\log X\le C(\log p)^{K'},
--   $$
--   and $E[Z_{\mathrm{target}}^N]\le C(\log p)^{K'}$.
--
--   This is the bound that makes the average cost polynomial.
--
--   Differences from the source:
--   - encoding: E and Pr under the sampling rule → uniform finite averages over shifts p N y; reason: this is the sampling rule without replacement
--   - encoding: NB log X = poly_{N,A}(log p) → NB log X ≤ C(log p)^{K'}, and E[Z^N] ≤ C(log p)^{K'}; reason: a bound is what the source's equals sign in this notation means, and the second clause restates the result
--   - encoding: For X = 1, Z_target = 1 → the display at X = 1: the integrals vanish and E[Z^N] = 1; reason: Z_target ≥ 1 by definition, so E[Z^N] = 1 is the same statement
--   - encoding: the constant C_N of Lemma 4.4 → a constant C_N > 0 chosen after N and before A; reason: the display uses Ψ_X with one constant depending only on N
-- source:
--   Kang, Lee, Provable Recovery from Integer Quotients: Improved Bounds for Nonlinear Hidden Number Problems, STOC 2027 submission (manuscript sha256 605f9dd3…), proof of Theorem 4.2, p.24 (PDF p.25)

import Mathlib
import Definitions.Def_IntQuotHNP_XiN
import Definitions.Def_IntQuotHNP_Sampling
import Definitions.Def_IntQuotHNP_DualLattice
import Definitions.Def_IntQuotHNP_MIHNPLattice
import Definitions.Def_IntQuotHNP_Psi

namespace IntQuotHNP

/-- **Proof of Theorem 4.2: `E[Z_target^N] − 1 = N∫_1^X u^{N−1} Pr[Z_target > u] du ≤ NB log X`.**
Kang, Lee, *Provable Recovery from Integer Quotients*, STOC 2027 submission (manuscript sha256
605f9dd3…), proof of Theorem 4.2, p.24 (PDF p.25): "Using 1 ≤ Z_target ≤ X and the tail-integral
identity from Section 3.3, we obtain E[Z^N_target] − 1 = N ∫_1^X u^{N−1} Pr[Z_target > u] du
≤ N ∫_1^X u^{N−1}Ψ_X(u) du ≤ NB log X = poly_{N,A}(log p). For X = 1, Z_target = 1."

For every `N ≥ 3` there is a constant `C_N > 0` in (7), and for every `A ≥ 0` there are `c, C, K, K'`
and `p₀`, such that for every prime `p ≥ p₀`, every integer `1 ≤ X < p` with
`X ≤ p^{ξ_N}(log p)^A` and every secret `y∗ ∈ ℤ_p`, with `B = c(log p)^K`, all four links of the
display hold:
1. `E[Z_target^N] − 1 = N ∫_1^X u^{N−1} Pr[Z_target > u] du`;
2. `N ∫_1^X u^{N−1} Pr[Z_target > u] du ≤ N ∫_1^X u^{N−1} Ψ_X(u) du`;
3. `N ∫_1^X u^{N−1} Ψ_X(u) du ≤ N B log X`;
4. `N B log X ≤ C(log p)^{K'}` and `E[Z_target^N] ≤ C(log p)^{K'}`.

**Formalization Note.** The expectation and the probability are uniform averages over
`shifts p N y∗` (sampling without replacement); `Z_target` is that of the lattice (6) of the sampled
input. `X < p` is the standing assumption of Definition 4.1. At `X = 1` the integrals vanish and the
display reads `E[Z_target^N] = 1`, the paper's "For X = 1, Z_target = 1". -/
theorem expected_ztarget_pow (N : ℕ) (hN : 3 ≤ N) :
    ∃ CN : ℝ, 0 < CN ∧ ∀ A : ℝ, 0 ≤ A → ∃ (c C : ℝ) (K K' p₀ : ℕ),
      ∀ p : ℕ, p.Prime → p₀ ≤ p → ∀ X : ℕ, 1 ≤ X → X < p →
        (X : ℝ) ≤ (p : ℝ) ^ xiN N * Real.log p ^ A → ∀ y, y < p →
          let Z : (Fin N → Fin p) → ℝ := fun t =>
            zTarget (latticeBasis (sampledInput p X N y t)) (vtar (sampledInput p X N y t)) p
          let B : ℝ := c * Real.log p ^ K
          avg (shifts p N y) (fun t => Z t ^ N) - 1 =
              N * ∫ u in (1 : ℝ)..X, u ^ (N - 1) * prob (shifts p N y) (fun t => u < Z t) ∧
            N * (∫ u in (1 : ℝ)..X, u ^ (N - 1) * prob (shifts p N y) (fun t => u < Z t)) ≤
              N * ∫ u in (1 : ℝ)..X, u ^ (N - 1) * Psi N CN X p u ∧
            N * (∫ u in (1 : ℝ)..X, u ^ (N - 1) * Psi N CN X p u) ≤ N * B * Real.log X ∧
            N * B * Real.log X ≤ C * Real.log p ^ K' ∧
            avg (shifts p N y) (fun t => Z t ^ N) ≤ C * Real.log p ^ K' := by sorry

end IntQuotHNP
