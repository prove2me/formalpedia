-- Prove2me | Theorems.Thm_IntQuotHNP_Supplement_theorem_6_2
-- name    : IntQuotHNP.Supplement.theorem_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:06:50.364919+00:00
-- url     : https://prove2.me/theorems/ff7ee029-2111-46b5-905b-89ea51304838
-- title:
--   Theorem 6.2 — HNPHM recovery: exact output, cost $\mathrm{poly}_N(\log p)(1+\Delta_N(1+\log X))$
-- statement:
--   This is the recovery theorem for the hidden number problem with hidden multipliers.
--
--   There are one deterministic machine and a step count $\tau(I)$ for every input such that:
--
--   1. on every promised input $I$ the machine outputs exactly the set of consistent secrets within $\tau(I)$ steps;
--   2. this set contains every consistent secret (in particular $y^*$) and has at most $2X+1$ elements;
--   3. the $m=2N+1$ vectors $\Phi(P_1),\dots,\Phi(P_m)$ of the polynomials (22) are linearly independent, and they have $d=3N+1$ coordinates ($k=2N+1$ error variables);
--   4. for every $N\ge1$ there are $C,K$ such that, for every prime $p$, every $1\le X<p$, every $y^*\in\mathbb Z_p\setminus\{0\}$ and every approximation rule, the average of $\tau$ over the sampled multipliers is at most
--   $$
--   C(\log p)^K\bigl(1+\Delta_N(1+\log X)\bigr),\qquad \Delta_N=\frac{X^{3N+1}}{(p-1)^N};
--   $$
--   5. for every $B\ge0$ this average is $\mathrm{poly}_{N,B}(\log p)$ throughout $X\le p^{\sigma_N}(\log p)^B$, $\sigma_N=N/(3N+1)$;
--   6. in this window the solution set equals $\{y^*\}$ with probability $1-o(1)$ as $p\to\infty$, uniformly in $X$, $y^*$ and the rule.
--
--   **Formalization Note** $\log$ is the natural logarithm, so $\log 1=0$; $p^{\sigma_N}$ and $(\log p)^B$ are real powers. The input code is the binary code of $p$, $X$, $N$, the approximations and the optional intervals; the output is the published canonical code of a finite set of natural numbers.
--
--   Differences from the source:
--   - reading: Algorithm 1 and its (deterministic) bit time → one Turing machine (Turing.TM2ComputableAux Bool Bool), chosen before N, B, p, X, y∗ and the rule, with a step count τ(I) bounding its steps (OutputsWithin), as in the published goal IntQuotHNP.theorem_4_2; reason: the paper names no machine; a multi-stack machine does the algorithm's arithmetic and bookkeeping with only a polylogarithmic loss per operation, which the poly_N(log p) factor absorbs, and it is the model of the published goal
--   - generalization: leading-bit intervals specified by the revealed bits → any integer intervals inside ℤ_p, checked in addition to (20); reason: the intervals are only checked by the reconstructor and do not enter the lattice; intervals cut out by revealed bits are instances
--   - encoding: input averages and probabilities over t∗₁, …, t∗_N independent and uniform in ℤ_p \ {0} → the published uniform averages avg, prob over the product set (ℤ_p \ {0})^N; reason: independent uniform sampling is the uniform law on the product
--   - encoding: the output equals {y∗} with probability 1 − o(1) as p → ∞ → for every η > 0 there is p₁ such that for primes p ≥ p₁ in the window the probability that the solution set differs from {y∗} is at most η; reason: definition of o(1), uniform in X, y∗ and the rule as the theorem states
-- source:
--   Kang, Lee, Provable Recovery from Integer Quotients: Improved Bounds for Nonlinear Hidden Number Problems, STOC 2027 submission (manuscript sha256 605f9dd3…), Theorem 6.2, p.37 (PDF p.38); Definition 6.1, p.37 (PDF p.38); eq. (22), p.38 (PDF p.39)

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_IntQuotHNP_Encoding
import Definitions.Def_IntQuotHNP_Sampling
import Definitions.Def_IntQuotHNP_Supplement_CoeffMap
import Definitions.Def_IntQuotHNP_Supplement_HNPHM

open HMBinPacking (OutputsWithin)

namespace IntQuotHNP

namespace Supplement

/-- **Theorem 6.2 (HNPHM recovery).**
Kang, Lee, *Provable Recovery from Integer Quotients: Improved Bounds for Nonlinear Hidden Number
Problems*, STOC 2027 submission (manuscript sha256 605f9dd3…), Theorem 6.2, p.37 (PDF p.38): "Fix
N ≥ 1 and put ∆_N = X^{3N+1}/(p − 1)^N, σ_N = N/(3N + 1). With the polynomials and reconstruction
procedure below, Algorithm 1 deterministically returns exactly the secrets satisfying the input
constraints on every promised input. Its output contains y∗ and has at most 2X + 1 elements. It
uses k = 2N + 1 error variables and a lattice of rank m = 2N + 1 in ambient dimension d = 3N + 1.
Its input-averaged bit cost is at most poly_N(log p)(1 + ∆_N(1 + log X)). (21) For every fixed
B ≥ 0, this cost is poly_{N,B}(log p) throughout X ≤ p^{σ_N}(log p)^B. In this window, the output
equals {y∗} with probability 1 − o(1) as p → ∞. These guarantees hold uniformly for every fixed y∗
and every approximation rule in the sampling model above."

There are one deterministic Turing machine `M` and a step count `τ(I)` for each input such that:
1. on every promised input `I`, `M` outputs exactly the set of consistent secrets within `τ(I)`
   steps;
2. that set contains every consistent secret (in particular `y∗`) and has at most `2X + 1`
   elements;
3. the `2N + 1` vectors `Φ(P₁), …, Φ(P_m)` of the paper's polynomials are linearly independent and
   there are `3N + 1` distinct nonconstant monomials (`k = m = 2N + 1`, `d = 3N + 1`);
4. for every `N ≥ 1` there are `C, K` such that, for every prime `p`, every `1 ≤ X < p`, every
   secret `y∗ ∈ ℤ_p \ {0}` and every admissible approximation rule, the average of `τ` over the
   sampled multipliers is at most `C(log p)^K (1 + Δ_N(1 + log X))`;
5. for every `N ≥ 1` and `B ≥ 0` there are `C, K` with that average at most `C(log p)^K` whenever
   also `X ≤ p^{σ_N}(log p)^B`;
6. for every `N ≥ 1`, `B ≥ 0` and `η > 0`, the probability that the output differs from `{y∗}` is
   at most `η` for all sufficiently large primes `p`, uniformly in `X` in the window, in `y∗` and
   in the rule.

**Formalization Note.** "Algorithm 1" is read as one Turing machine (Mathlib's
`Turing.TM2ComputableAux Bool Bool`, as in the published goal `IntQuotHNP.theorem_4_2`), chosen
before `N`, `B`, `p`, `X`, `y∗` and the rule; bit time is its step count (`OutputsWithin`). Input and
output are `hnphmEncodeInput` and the published `encodeSecrets`. Input averages and probabilities
are the published uniform averages `avg`, `prob` over `hnphmMults p N` (independent uniform
multipliers in `ℤ_p \ {0}`). `log` is the natural logarithm (`log 1 = 0`); `p^{σ_N}` and
`(log p)^B` are `Real.rpow`. -/
theorem theorem_6_2 :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (τ : HNPHMInput → ℕ),
      (∀ I : HNPHMInput, HNPHMPromised I →
        OutputsWithin M (hnphmEncodeInput I) (encodeSecrets (hnphmSolutionSet I)) (τ I)) ∧
      (∀ I : HNPHMInput, HNPHMPromised I →
        (∀ y t, HNPHMConsistent I y t → y ∈ hnphmSolutionSet I) ∧
          (hnphmSolutionSet I).card ≤ 2 * I.X + 1) ∧
      (∀ I : HNPHMInput, HNPHMPromised I →
        LinearIndependent ℝ (fun h => Phi I.X (hnphmPolys I) (hnphmPolys I h)) ∧
          (mons (hnphmPolys I)).card = 3 * I.N + 1) ∧
      (∀ N : ℕ, 1 ≤ N → ∃ (C : ℝ) (K : ℕ),
        ∀ p : ℕ, p.Prime → ∀ X : ℕ, 1 ≤ X → X < p → ∀ y : ℕ, 1 ≤ y → y < p →
          ∀ rule : HNPHMRule p N, HNPHMIsRule p X N y rule →
            avg (hnphmMults p N) (fun t => (τ (hnphmSampled p X N rule t) : ℝ)) ≤
              C * Real.log p ^ K * (1 + hnphmDelta N X p * (1 + Real.log X))) ∧
      (∀ N : ℕ, 1 ≤ N → ∀ B : ℝ, 0 ≤ B → ∃ (C : ℝ) (K : ℕ),
        ∀ p : ℕ, p.Prime → ∀ X : ℕ, 1 ≤ X → X < p →
          (X : ℝ) ≤ (p : ℝ) ^ sigmaN N * Real.log p ^ B → ∀ y : ℕ, 1 ≤ y → y < p →
          ∀ rule : HNPHMRule p N, HNPHMIsRule p X N y rule →
            avg (hnphmMults p N) (fun t => (τ (hnphmSampled p X N rule t) : ℝ)) ≤
              C * Real.log p ^ K) ∧
      (∀ N : ℕ, 1 ≤ N → ∀ B : ℝ, 0 ≤ B → ∀ η : ℝ, 0 < η → ∃ p₁ : ℕ,
        ∀ p : ℕ, p.Prime → p₁ ≤ p → ∀ X : ℕ, 1 ≤ X → X < p →
          (X : ℝ) ≤ (p : ℝ) ^ sigmaN N * Real.log p ^ B → ∀ y : ℕ, 1 ≤ y → y < p →
          ∀ rule : HNPHMRule p N, HNPHMIsRule p X N y rule →
            prob (hnphmMults p N) (fun t => hnphmSolutionSet (hnphmSampled p X N rule t) ≠ {y}) ≤
              η) := by sorry

end Supplement

end IntQuotHNP
