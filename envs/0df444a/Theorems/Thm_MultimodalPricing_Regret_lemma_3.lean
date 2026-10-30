-- Prove2me | Theorems.Thm_MultimodalPricing_Regret_lemma_3
-- name    : MultimodalPricing.Regret.lemma_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T08:05:09.930423+00:00
-- url     : https://prove2.me/theorems/18f45540-0534-47e0-b61f-858babd2f9bd
-- title:
--   Lemma 3 — cumulative within-bin performance
-- statement:
--   There is a constant $B>0$, chosen before all instance parameters, horizons and sample spaces, such that for every smooth demand $f\in\Sigma^k([a,b];C)$ on $0\le a\le b$, $\Delta\ge C(b-a)^k$ and integers $1\le t\le T$, the first $t$ local calls of BiasedLinearBandit starting from empty history, with $\delta=1/T^2$, satisfy
--   $$\frac1t\sum_{n<t}\big[\max_{p\in[a,b]}pf(p)-p_n f(p_n)\big]\le(\Delta+\max\{1,C\}/\sqrt t)3k\log(2kT)$$
--   except on a set of outer probability at most $B/T$. Observations follow the sequential kernel law. Calls are counted in local-visit order, and every price allowed by the undefined first-call branch and every subsequent maximizing tie are included. This is a fixed-$t$ one-bin assertion, not a simultaneous assertion at a random visit count. The printed absence of a $p_{\max}$ factor is retained.
--
--   Differences from the source:
--   - generalization: economic price interval → finite nonnegative real endpoints with 0 ≤ a ≤ b, including a singleton; reason: makes the economic nonnegative-price convention explicit, as required by the revenue comparison on p. 32; singleton intervals are additionally admitted
--   - encoding: (k−1) derivatives on the closed price interval → a tower of successive HasDerivWithinAt derivatives, with order zero equal to f on the interval; reason: uses one-sided endpoint derivatives, imposes no condition outside the interval, and at k=1 requires only the printed bounded Lipschitz condition
--   - reading: the price-conditioned mean on p. 9 and full-history centered noise on p. 32 → a measurable probability kernel on finite observation histories and current price, supported in [0,1] with mean f(p), realized by conditional-law integral identities; reason: makes the operational sequential model explicit without independence or a concentration assumption
--   - generalization: randomized decisions based on observed history → decisions measurable in any predecision filtration for which the same history-and-price kernel is the conditional demand law; reason: the observed-history filtration with private randomization is a special case; no future demand may invalidate the conditional law
--   - encoding: rounds 1 through t and vector coordinates 0 through k−1 → rounds in Finset.range t, ordered lists retaining repetitions, and vectors Fin k → ℝ; reason: reindexing changes no observation or coefficient
--   - reading: centered features in Algorithm 2, conflicting with uncentered features in the explanatory p. 13 prose → features (1,p−a,…,(p−a)^(k−1)) as explicitly printed in Algorithm 2; reason: the algorithm and Lemma 1 agree; the inconsistent prose identity is recorded as finding I5
--   - generalization: Algorithm 2 has no defined radius on empty history because it uses log(0) → every feasible first price is admitted, followed by exactly the printed nonempty-history maximizations; reason: the assertion covers every completion of the undefined branch, rather than selecting a favorable repair
--   - encoding: maximum expected revenue on a closed interval → sSup of the image of p ↦ p f(p); reason: Smooth implies continuity on a nonempty compact interval, so this supremum is finite and attained
--   - encoding: with probability at least 1−δ or 1−O(1/T) → outer measure of the strict bad event at most δ or B/T; reason: agrees on measurable events and avoids assuming measurability of an uncountable supremum
--   - reading: failure probability O(T⁻¹) → a single positive B quantified before k,C,a,b,Δ,T,t and the stochastic instance; reason: uses the uniform reading prescribed in the brief; no instance-dependent hidden failure constant
--   - encoding: consecutive calls in one selected bin → a local observation sequence whose prefixes start empty and append each demand; reason: intervening visits to other bins are represented by the local predecision information; no random stopping-time guarantee is asserted
-- source:
--   Wang, Chen, Simchi-Levi, Multi-Modal Dynamic Pricing, https://doi.org/10.1287/mnsc.2020.3819, supplied artifact (published metadata; SSRN 3489355 footer), Lemma 3, printed/PDF p. 14; companion, pp. 33–34

import Definitions.Def_MultimodalPricing_Regret_Regret

open MeasureTheory MultimodalPricing.Regret
universe u

namespace MultimodalPricing.Regret

theorem lemma_3 :
    ∃ B : ℝ, 0 < B ∧
      ∀ (k T t : ℕ) (C a b Δ : ℝ) (f : ℝ → ℝ),
      Smooth k C a b f → 0 ≤ a → C * (b - a) ^ k ≤ Δ →
      1 ≤ t → t ≤ T →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (O : Observation Ω),
        IsObservation μ t a b f O →
        LocalRun μ t k a b C Δ (1 / (T : ℝ) ^ 2) O →
        μ {ω | (Δ + max 1 C / Real.sqrt t) * (3 * k * Real.log (2 * k * T)) <
          averagePseudoRegret t a b f O.price ω} ≤ ENNReal.ofReal (B / T) := by sorry

end MultimodalPricing.Regret
