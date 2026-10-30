-- Prove2me | Theorems.Thm_MultimodalPricing_Regret_theorem_1
-- name    : MultimodalPricing.Regret.theorem_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T08:05:01.250296+00:00
-- url     : https://prove2.me/theorems/efc71c58-949b-4b64-b7b3-03084d632af9
-- title:
--   Theorem 1 — high-probability multimodal pricing regret
-- statement:
--   Fix $k\ge1$, $C>0$ and finite nonnegative endpoints $0\le p_{\min}\le p_{\max}$, and write $L=p_{\max}-p_{\min}$. There are $A,B>0$ and an integer $m\ge0$, depending only on these fixed parameters, such that for every integer $T\ge1$ with $T\ge L^{2k+1}$, every $f\in\Sigma^k([p_{\min},p_{\max}];C)$, every admissible sequential demand law, every algorithm run and every bounded counterfactual coupling with the prescribed means, Algorithms 1–2 with $N=\lceil T^{1/(2k+1)}\rceil$ and $\Delta=C(L/N)^k$ satisfy
--   $$\mathbb P^*\!\left(R_T>A\sqrt T\log(2T)^m+3k\log(2kT)[4\max\{1,C\}+CL^k]T^{(k+1)/(2k+1)}\right)\le B/T.$$
--   Here $R_T$ is the supremum of realized fixed-price cumulative revenues minus realized algorithm revenue on the same sample path. All maximizing ties and all feasible completions of the undefined first call are included. The constants precede the horizon, demand, probability space, law and choices. This also yields the printed $\widetilde O(T^{(k+1)/(2k+1)})$ upper rate on the same good event: $1/2\le(k+1)/(2k+1)$, and for fixed $k$ the factor $\log(2kT)$ is $O(\log(2T))$. No extra theorem is assumed for that consequence.
--
--   This is the source claim, not a completed proof. Findings I2–I4 record undefined initialization, a coefficient derivation gap, and the realized-benchmark obstruction; none is repaired inside the target.
--
--   Differences from the source:
--   - generalization: economic price interval → finite nonnegative real endpoints with 0 ≤ a ≤ b, including a singleton; reason: makes the economic nonnegative-price convention explicit, as required by the revenue comparison on p. 32; singleton intervals are additionally admitted
--   - encoding: (k−1) derivatives on the closed price interval → a tower of successive HasDerivWithinAt derivatives, with order zero equal to f on the interval; reason: uses one-sided endpoint derivatives, imposes no condition outside the interval, and at k=1 requires only the printed bounded Lipschitz condition
--   - reading: the price-conditioned mean on p. 9 and full-history centered noise on p. 32 → a measurable probability kernel on finite observation histories and current price, supported in [0,1] with mean f(p), realized by conditional-law integral identities; reason: makes the operational sequential model explicit without independence or a concentration assumption
--   - generalization: randomized decisions based on observed history → decisions measurable in any predecision filtration for which the same history-and-price kernel is the conditional demand law; reason: the observed-history filtration with private randomization is a special case; no future demand may invalidate the conditional law
--   - encoding: rounds 1 through t and vector coordinates 0 through k−1 → rounds in Finset.range t, ordered lists retaining repetitions, and vectors Fin k → ℝ; reason: reindexing changes no observation or coefficient
--   - reading: centered features in Algorithm 2, conflicting with uncentered features in the explanatory p. 13 prose → features (1,p−a,…,(p−a)^(k−1)) as explicitly printed in Algorithm 2; reason: the algorithm and Lemma 1 agree; the inconsistent prose identity is recorded as finding I5
--   - generalization: Algorithm 2 has no defined radius on empty history because it uses log(0) → every feasible first price is admitted, followed by exactly the printed nonempty-history maximizations; reason: the assertion covers every completion of the undefined branch, rather than selecting a favorable repair
--   - encoding: with probability at least 1−δ or 1−O(1/T) → outer measure of the strict bad event at most δ or B/T; reason: agrees on measurable events and avoids assuming measurability of an uncountable supremum
--   - reading: the p. 9 display has no expectation signs and takes a fixed-price supremum outside the sum → the literal realized supremum over a common response field, universally over its couplings with measurable fixed-price sections and actual sequential observations; reason: preserves the stronger displayed benchmark; pointwise smooth means do not supply uniform concentration, as recorded in I4
--   - reading: O-tilde(sqrt T) and failure O(T⁻¹) → positive A,B and natural m after k,C,endpoints but before T,f,law and tie choices, using log(2T)^m only for the unspecified term; reason: spells out uniform asymptotics without changing the explicit leading coefficient or replacing every admissible T by an eventual threshold
--   - reading: Algorithm 1 labels equal bins [a_j,b_{j+1}] without defining that right endpoint → [a+jL/N,a+(j+1)L/N]; reason: implements the explicit equal partition instruction
--   - encoding: the displayed bound equals an O-tilde(T^((k+1)/(2k+1))) rate → the exact bound is the theorem conclusion and its rate consequence is documented above; reason: the consequence follows directly for T≥1 and fixed k without a further hypothesis
-- source:
--   Wang, Chen, Simchi-Levi, Multi-Modal Dynamic Pricing, https://doi.org/10.1287/mnsc.2020.3819, supplied artifact (published metadata; SSRN 3489355 footer), Theorem 1, equation (3), printed/PDF p. 11; benchmark p. 9; proof pp. 14–15

import Definitions.Def_MultimodalPricing_Regret_Regret

open MeasureTheory MultimodalPricing.Regret
universe u

namespace MultimodalPricing.Regret

theorem theorem_1
    (k : ℕ) (hk : 1 ≤ k) (C pmin pmax : ℝ) (hC : 0 < C)
    (hprice : 0 ≤ pmin) (hend : pmin ≤ pmax) :
    ∃ A B : ℝ, ∃ m : ℕ, 0 < A ∧ 0 < B ∧
      ∀ T : ℕ, 1 ≤ T → (pmax - pmin) ^ (2 * k + 1) ≤ (T : ℝ) →
      ∀ f : ℝ → ℝ, Smooth k C pmin pmax f →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (O : Observation Ω) (j : ℕ → Ω → ℕ) (D : ℕ → ℝ → Ω → ℝ),
        IsObservation μ T pmin pmax f O →
        AlgorithmRun μ k T C pmin pmax O j →
        IsResponseField μ T pmin pmax f O D →
        μ {ω | A * Real.sqrt T * Real.log (2 * T) ^ m +
            3 * k * Real.log (2 * k * T) *
              (4 * max 1 C + C * (pmax - pmin) ^ k) *
              (T : ℝ) ^ (((k : ℝ) + 1) / (2 * k + 1)) <
          realizedRegret T pmin pmax O.price O.demand D ω}
          ≤ ENNReal.ofReal (B / T) := by sorry

end MultimodalPricing.Regret
