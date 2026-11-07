-- Prove2me | Theorems.Thm_IntQuotHNP_theorem_4_2
-- name    : IntQuotHNP.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:53:59.433494+00:00
-- url     : https://prove2.me/theorems/75535926-f008-4738-85ba-4566f06aeea4
-- title:
--   Theorem 4.2 — MIHNP recovery: exact output, expected bit time $\mathrm{poly}_{N,A}(\log p)$ and unique recovery for $X\le p^{\xi_N}(\log p)^A$
-- statement:
--   There are one deterministic Turing machine $M$ and a step count $\tau(I)$ for each input such that:
--
--   1. on every promised input $I$, $M$ outputs exactly the set of secrets satisfying (4) with $x\in B$, within $\tau(I)$ steps;
--   2. that set contains every consistent secret, in particular $y^*$, and has at most $X$ elements;
--   3. the $N(N+1)/2$ rows of the lattice (6) are linearly independent in dimension $d=N(N+1)/2$, with $k=N$ error variables;
--   4. for every $N\ge3$ there is $C'>0$, and for every $A\ge0$ there are $C,K,p_0$, such that for every prime $p\ge p_0$, every integer $1\le X<p$ with $X\le p^{\xi_N}(\log p)^A$ and every $y^*\in\mathbb Z_p$, over the shifts sampled uniformly without replacement from $\mathbb Z_p\setminus\{[-y^*]_p\}$:
--   $$
--   E[\tau]\le C(\log p)^K,\qquad\Pr[\text{output}\ne\{y^*\}]\le C'\frac{X^N}{p^{N-1}},
--   $$
--   and every sampled input is promised, with $y^*$ in its output;
--   5. for every $N\ge3$, $A\ge0$ and $\eta>0$, that failure probability is at most $\eta$ for all sufficiently large primes $p$, uniformly in $X$ in the range and in $y^*$.
--
--   Here $\xi_N$ is (5). This takes the provable recovery range of MIHNP from $X\le p^{1/3-\varepsilon}$ to $X\le p^{1/2-\varepsilon}$.
--
--   Differences from the source:
--   - reading: Algorithm 1, with the polynomials and reconstructor below → there exists one Turing machine, chosen before N, A, p, X, y*, with the output and cost guarantees; reason: writing LLL and the subdivision search as a machine inside the statement is not checkable by a reader; Algorithm 1 is one uniform algorithm with N in its input, and clause 3 keeps the method-specific lattice claim on (6)
--   - reading: expected bit running time → the average over the shifts of a step bound τ(I) of the machine (OutputsWithin); reason: the paper names no machine; steps of a fixed multi-stack machine and bit operations are polynomially related, and the bounds are closed under polynomials; the machine is deterministic, and τ can be taken to be the exact halting time
--   - encoding: expectation and probability over the sampled shifts → uniform finite averages over shifts p N y; reason: this is the sampling rule without replacement; N < p for large p makes the set nonempty
--   - encoding: the standing 1 ≤ X < p of Definition 4.1 → the hypothesis X < p in clause 4; reason: the source's own standing assumption, and implied by X ≤ p^{ξ_N}(log p)^A for large p
--   - encoding: 1 − o(1) → ∀ η > 0, ∃ p₁, uniformly in X and y*; reason: the source's limit, stated uniformly as it says
--   - encoding: the guarantees on promised inputs applied to the sampled inputs, which the source treats as MIHNP inputs → clause 4 also states that every sampled input is promised; reason: implicit in the source (y* with x*_i = z*_i − v_i satisfies (4), and N < p for large p); stating it changes no instance
-- source:
--   Kang, Lee, Provable Recovery from Integer Quotients: Improved Bounds for Nonlinear Hidden Number Problems, STOC 2027 submission (manuscript sha256 605f9dd3…), Theorem 4.2, p.22 (PDF p.23)

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_IntQuotHNP_MIHNPInput
import Definitions.Def_IntQuotHNP_Encoding
import Definitions.Def_IntQuotHNP_XiN
import Definitions.Def_IntQuotHNP_Sampling
import Definitions.Def_IntQuotHNP_MIHNPLattice

open HMBinPacking (OutputsWithin)

namespace IntQuotHNP

/-- **Theorem 4.2 (MIHNP recovery).**
Kang, Lee, *Provable Recovery from Integer Quotients: Improved Bounds for Nonlinear Hidden Number
Problems*, STOC 2027 submission (manuscript sha256 605f9dd3…), Theorem 4.2, p.22 (PDF p.23): "Fix
N ≥ 3 and A ≥ 0. Let k_N be the nonnegative integer satisfying k_N(k_N + 1) ≤ N < (k_N + 1)(k_N + 2),
and put ξ_N = (N + k_N² − 1)/(2(N + k_N(k_N + 1))). (5) Algorithm 1, with the polynomials and
reconstructor below, deterministically returns exactly the secrets satisfying (4) with x ∈ B on
every promised input. Its output contains y∗ and has at most X elements. It uses k = N error
variables and a lattice of rank m = N(N + 1)/2 in ambient dimension d = m. For sufficiently large p
and X ≤ p^{ξ_N}(log p)^A, its expected bit running time is poly_{N,A}(log p), and its output equals
{y∗} with probability at least 1 − O_N(X^N/p^{N−1}) = 1 − o(1). The expectation and probability are
over the shifts sampled above, uniformly for every fixed y∗."

There are one deterministic Turing machine `M` and a step count `τ(I)` for each input such that:
1. on every promised input `I`, `M` outputs exactly the set of secrets satisfying (4) with `x ∈ B`
   within `τ(I)` steps;
2. that set contains every consistent secret (in particular `y∗`) and has at most `X` elements;
3. the `N(N + 1)/2` rows of the lattice (6) are linearly independent in dimension `N(N + 1)/2`;
4. for every `N ≥ 3` there is `C' > 0`, and for every `A ≥ 0` there are `C, K, p₀`, such that for
   every prime `p ≥ p₀`, every integer `1 ≤ X < p` with `X ≤ p^{ξ_N}(log p)^A` and every secret
   `y∗ ∈ ℤ_p`: the expected running time over the sampled shifts is at most `C(log p)^K`; every
   sampled input is promised and its output contains `y∗`; and the output differs from `{y∗}` with
   probability at most `C' X^N/p^{N−1}`;
5. for every `N ≥ 3`, `A ≥ 0` and `η > 0`, that probability is at most `η` for all sufficiently
   large primes `p`, uniformly in `X` in the range and in `y∗` (the `1 − o(1)`).

**Formalization Note.** "Algorithm 1" is read as one Turing machine `M` (Mathlib's
`Turing.TM2ComputableAux Bool Bool`), chosen before `N`, `A`, `p`, `X`, `y∗`; bit time is its step
count (`OutputsWithin`), which is polynomially related to bit operations. Since `M` is
deterministic, the expected running time is the average of `τ` over the sampled shifts; `τ` can be
taken to be the exact halting time. Input and output are the binary codes `encodeInput`,
`encodeSecrets`. Expectation and probability are uniform averages over `shifts p N y∗`. `log` is the
natural logarithm; `p^{ξ_N}` and `(log p)^A` are `Real.rpow`. `X < p` is Definition 4.1's standing
assumption (implied for large `p` by `X ≤ p^{ξ_N}(log p)^A`). -/
theorem theorem_4_2 :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (τ : MIHNPInput → ℕ),
      (∀ I : MIHNPInput, IsPromised I →
        OutputsWithin M (encodeInput I) (encodeSecrets (solutionSet I)) (τ I)) ∧
      (∀ I : MIHNPInput, IsPromised I →
        (∀ y x, Consistent I y x → y ∈ solutionSet I) ∧ (solutionSet I).card ≤ I.X) ∧
      (∀ I : MIHNPInput, IsPromised I →
        LinearIndependent ℝ (latticeBasis I) ∧ Fintype.card (Mon I.N) = I.N * (I.N + 1) / 2) ∧
      (∀ N : ℕ, 3 ≤ N → ∃ C' : ℝ, 0 < C' ∧ ∀ A : ℝ, 0 ≤ A → ∃ (C : ℝ) (K p₀ : ℕ),
        ∀ p : ℕ, p.Prime → p₀ ≤ p → ∀ X : ℕ, 1 ≤ X → X < p →
          (X : ℝ) ≤ (p : ℝ) ^ xiN N * Real.log p ^ A → ∀ y, y < p →
            avg (shifts p N y) (fun t => (τ (sampledInput p X N y t) : ℝ)) ≤ C * Real.log p ^ K ∧
            (∀ t ∈ shifts p N y, IsPromised (sampledInput p X N y t) ∧
              y ∈ solutionSet (sampledInput p X N y t)) ∧
            prob (shifts p N y) (fun t => solutionSet (sampledInput p X N y t) ≠ {y}) ≤
              C' * (X : ℝ) ^ N / (p : ℝ) ^ (N - 1)) ∧
      (∀ N : ℕ, 3 ≤ N → ∀ A : ℝ, 0 ≤ A → ∀ η : ℝ, 0 < η → ∃ p₁ : ℕ,
        ∀ p : ℕ, p.Prime → p₁ ≤ p → ∀ X : ℕ, 1 ≤ X → X < p →
          (X : ℝ) ≤ (p : ℝ) ^ xiN N * Real.log p ^ A → ∀ y, y < p →
            prob (shifts p N y) (fun t => solutionSet (sampledInput p X N y t) ≠ {y}) ≤ η) := by sorry

end IntQuotHNP
