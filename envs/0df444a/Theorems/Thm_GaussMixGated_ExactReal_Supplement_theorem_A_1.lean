-- Prove2me | Theorems.Thm_GaussMixGated_ExactReal_Supplement_theorem_A_1
-- name    : GaussMixGated.ExactReal.Supplement.theorem_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:09:13.460255+00:00
-- url     : https://prove2.me/theorems/be4280f1-fa18-4c41-9531-1bf227e71d99
-- title:
--   Theorem A.1 — fixed-precision observations and smoothed TV
-- statement:
--   There are universal integers $C,c,p\ge1$, one fixed finite-bit trainer and one fixed rational sampler with the following property. Let $d,k\ge1$, let $\alpha,\varepsilon,\delta$ be rational with $0<\alpha\le1$ and $0<\varepsilon,\delta<1/2$, and let
--   $$P=\sum_{j=1}^{k_0}w_jN(\mu_j,I_d),\quad k_0\le k,\quad w_j\ge\alpha,\quad\sum_jw_j=1.$$
--   The means $\mu_j\in\mathbb R^d$ are unrestricted and may coincide. Define $A,\bar A,b,Q_b$ as above and $\tau=\varepsilon/(100d)$. The trainer receives $(d,k,\alpha,\varepsilon,\delta)$ and accesses independent observations only through $Q_b(X)$ with $X\sim P$. On every observation and training-coin tape it halts, reads at most $A^c$ observations, and emits a finite binary description $D$. If $L$ is the total binary length of the parameters and observations fetched on that run, then
--   $$\text{training bit cost},\ |D|,\ \text{per-output bit cost},\ \text{per-output random-bit count}\ \le p(AL)^p.$$
--   All four bounds hold on every outcome, and the sampler halts with a valid $d$-rational output on every fresh coin tape. It reads $D$ and fair coins only and makes no further target observation. Write $Q$ for its measurable output law on $\mathbb R^d$. With probability at least $1-\delta$ over training,
--   $$\operatorname{TV}\!\left(Q*N(0,\tau^2I_d),P\right)\le\varepsilon.$$
--   Equivalently, adding one independent ideal Gaussian vector to the rational output gives the continuous law in this display. That Gaussian draw is an additional randomness source, outside the finite-bit operation count. Theorem A.1 is a companion learner and is not used in the proof of the mission's exact-real goal.
--
--   Differences from the source:
--   - encoding: a finite-bit algorithm returns a finite rational randomized program → one fixed log-cost rational RAM trainer with an encoded quantized-observation instruction and one fixed observation-free rational RAM sampler interpreting its emitted bit string; reason: this makes the source bit model and program interface explicit; rational RAM bit costs and bit computation have polynomial simulation overhead, absorbed by the universal polynomial
--   - encoding: universal integers C,c and poly(A,L) resource bounds → positive natural constants C,c,p precede all instance data and all four costs are bounded by p(AL)^p; reason: A and L are bounded below by one on the stated domain, so this envelope captures a universal polynomial without changing any instance
--   - encoding: integer ceilings in the definition of b → natural ceilings for the positive quantities defining Abar and b; reason: all ceiling arguments are positive on the parameter domain, so the values agree
--   - encoding: with probability at least 1-delta over training the smoothed output law is within epsilon in TV → a measurable event contained in the success set has joint iid-sample and fair-coin probability at least 1-delta, with measurable sampler maps and valid rational output on every tape; reason: the inner-measure formulation avoids assuming measurability of the TV-valued training success predicate and preserves the source probabilistic guarantee
-- source:
--   Zheng, Xie, He, Learning Finite Gaussian Location Mixtures via Gated Moments and Posterior Covers, STOC 2027 submission #36 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/36.pdf, Theorem A.1, PDF p. 23 (printed p. 21)

import Mathlib
import Definitions.Def_FoundationsRL_DECLower_tvDist
import Definitions.Def_GaussMixGated_ExactReal_Machine
import Definitions.Def_GaussMixGated_ExactReal_Supplement_Model

open MeasureTheory BlottoFPTAS.Main

namespace GaussMixGated.ExactReal.Supplement

/-- Theorem A.1, PDF p. 23 (printed p. 21), including every-outcome resource caps
from PDF p. 38. The finite-bit sampler receives only the emitted description and fair coins.
The Gaussian convolution is an additional ideal draw, outside finite-bit computation. -/
theorem theorem_A_1 :
    ∃ C c p : ℕ, 1 ≤ C ∧ 1 ≤ c ∧ 1 ≤ p ∧
    ∃ (T : BitProgram) (S : BitRAM.Program),
    ∀ (d k : ℕ), 1 ≤ d → 1 ≤ k →
    ∀ (α ε δ : ℚ), 0 < α → α ≤ 1 → 0 < ε → ε < 1 / 2 → 0 < δ → δ < 1 / 2 →
    ∀ (s : ℕ) (w : Fin s → ℝ) (μ : Fin s → EuclideanSpace ℝ (Fin d)),
      IsMixingMeasure k s w → (∀ j, (α : ℝ) ≤ w j) →
      (∀ (xs : ℕ → EuclideanSpace ℝ (Fin d)) (coins : ℕ → Bool),
        BitHalts T (parameterCode d k α ε δ)
          (answerCode (precision C d k α ε δ) xs) coins ∧
        let result := trainFinal T C d k α ε δ xs coins
        let D := result.core.out
        let B := costBound p (sizeA d k α ε δ) (encodingLength result)
        (result.observations : ℝ) ≤ sizeA d k α ε δ ^ c ∧
        (result.core.cost : ℝ) ≤ B ∧
        (D.length : ℝ) ≤ B ∧
        Measurable (discreteOutput d S D) ∧
        ∀ fresh : ℕ → Bool,
          BitRAM.Halts S D fresh ∧
          (BitRAM.decodeAlloc d (BitRAM.output S D fresh)).isSome = true ∧
          (BitRAM.bitCost S D fresh : ℝ) ≤ B ∧
          (BitRAM.randomBits S D fresh : ℝ) ≤ B) ∧
      ∃ E : Set ((ℕ → EuclideanSpace ℝ (Fin d)) × (ℕ → Bool)),
        MeasurableSet E ∧
        (∀ ω ∈ E,
          FoundationsRL.DECLower.tvDist
            (smoothedLaw d S (trainFinal T C d k α ε δ ω.1 ω.2).core.out
              ((ε : ℝ) / (100 * (d : ℝ))))
            (mixtureLaw d s 1 w μ) ≤ (ε : ℝ)) ∧
        ENNReal.ofReal (1 - (δ : ℝ)) ≤
          ((iidTape (mixtureLaw d s 1 w μ)).prod BitRAM.coinTape) E := by sorry

end GaussMixGated.ExactReal.Supplement
