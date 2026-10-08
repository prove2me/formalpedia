-- Prove2me | Theorems.Thm_FournierGuillin_Conc_lemma_12
-- name    : FournierGuillin.Conc.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:23:06.308054+00:00
-- url     : https://prove2.me/theorems/e5c20125-eee9-43ee-a1c4-417ecabab963
-- title:
--   Lemma 12, p. 14 — Binomial(N, p) deviation bounds via f and the Laplace transform E e^{−θX}
-- statement:
--   Let $N\ge1$, let $s\in(0,1]$, and let $X$ be Binomial($N,s$)-distributed. With $f$ as in Notation 7:
--
--   1. $\mathbb P\big[|X-Ns|\ge Nsz\big]\le\big(\mathbf 1_{\{s(1+z)\le1\}}+\mathbf 1_{\{z\le1\}}\big)\exp(-Nsf(z))$ for all $z>0$;
--   2. $\mathbb P\big[|X-Ns|\ge Nsz\big]\le Ns$ for all $z>1$;
--   3. $\mathbb E\,e^{-\theta X}=(1-s+se^{-\theta})^N\le\exp(-Ns(1-e^{-\theta}))$ for all $\theta>0$.
--
--   These bounds control $N\mu_N(B_n)$, which is Binomial($N,\mu(B_n)$)-distributed, in the proof of Lemma 13 and of display (6).
--
--   **Formalization Note** The page calls the success probability $p$; here it is $s$, because $p$ is the transport exponent of the mission. The law is Mathlib's `binomial N s` on $\mathbb N$ with `s : unitInterval`. **Added hypotheses:** $N\ge1$ and $s>0$, implicit on the page. Without them (a) and (b) are false: at $s=0$ the event of (b) has probability $1$ while the bound is $0$, and at $N=0$ the event of (a) has probability $1$ while the bound can be $0$. Every use of the lemma has $N\ge1$ and a positive success probability. The expectation in (c) is a lower Lebesgue integral.
-- source:
--   Fournier & Guillin, arXiv:1312.2128v1, Lemma 12, p. 14; proof p. 14

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_empiricalDistribution
import Definitions.Def_FournierGuillin_Conc_Setting
open MeasureTheory WassersteinDRO.Duality
open scoped ENNReal NNReal

namespace FournierGuillin.Conc

/-- Lemma 12 (p. 14): for `X` Binomial(`N`, `s`)-distributed (the page's success probability `p` is
`s` here), with `N ≥ 1` and `s > 0` (implicit on the page, needed for (a), (b)):
(a) `ℙ[|X - Ns| ≥ Nsz] ≤ (1_{s(1+z) ≤ 1} + 1_{z ≤ 1}) exp(-Ns f(z))` for `z > 0`;
(b) `ℙ[|X - Ns| ≥ Nsz] ≤ Ns` for `z > 1`;
(c) `E exp(-θX) = (1 - s + s e^{-θ})^N ≤ exp(-Ns(1 - e^{-θ}))` for `θ > 0`. -/
theorem lemma_12 (N : ℕ) (hN : 1 ≤ N) (s : unitInterval) (hs : 0 < (s : ℝ)) :
    (∀ z : ℝ, 0 < z →
      ProbabilityTheory.binomial N s {k : ℕ | (N : ℝ) * s * z ≤ |(k : ℝ) - N * s|} ≤
        ENNReal.ofReal (((if (s : ℝ) * (1 + z) ≤ 1 then 1 else 0) + (if z ≤ 1 then 1 else 0)) *
          Real.exp (-((N : ℝ) * s * bennettF z)))) ∧
    (∀ z : ℝ, 1 < z →
      ProbabilityTheory.binomial N s {k : ℕ | (N : ℝ) * s * z ≤ |(k : ℝ) - N * s|} ≤
        ENNReal.ofReal ((N : ℝ) * s)) ∧
    (∀ θ : ℝ, 0 < θ →
      ∫⁻ k : ℕ, ENNReal.ofReal (Real.exp (-(θ * k))) ∂ProbabilityTheory.binomial N s =
          ENNReal.ofReal ((1 - s + s * Real.exp (-θ)) ^ N) ∧
        (1 - (s : ℝ) + s * Real.exp (-θ)) ^ N ≤ Real.exp (-((N : ℝ) * s * (1 - Real.exp (-θ)))))
    := by sorry

end FournierGuillin.Conc
