-- Prove2me | Theorems.Thm_MaxWeightInstab_eq_16
-- name    : MaxWeightInstab.eq_16
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:14:37.941807+00:00
-- url     : https://prove2.me/theorems/28bf88d0-1f73-43fb-a26f-5ef959da7144
-- title:
--   Display (16) — $\mathbb P(G_M)\ge 1-e^{-\eta T}$
-- statement:
--   Let $a,J,\nu$ satisfy (4) and (5) and let $\gamma$ satisfy (11). Let the external arrival patterns of successive time units of the network of Figure 1 be independent, each with the arrival law (independent Bernoulli$(a/J)$ at the $2J$ external queues). For every $\varepsilon>0$ there exist $\eta>0$ and $C$ such that, for every $M$ with $T\ge C$ ($T=2M/((1-a)(1-r_{\boldsymbol\rho}))$, (14)),
--
--   $$
--   \mathbb P(G_M)\ \ge\ 1-e^{-\eta T},
--   $$
--
--   where $G_M$ is the event (15): all $2J$ external arrival counts stay within $\varepsilon bT$ of their means on every window of $[0,T]$.
--
--   It is the probabilistic input of the proof of Theorem 1: on $G_M$ the deterministic Proposition 1 applies.
--
--   **Formalization Note** The statement holds on any probability space carrying the arrival vectors; the arrival vector of time unit $n$ is $E_n$.
--
--   Differences from the source:
--   - generalization: ε ∈ (0, ε₀), the section's standing choice (p.6) → every ε > 0; reason: (16) is Lemma 1 with δ = εb > 0, which holds for every ε > 0; specializes to the source
--   - reading: arrivals "at rate a, that choose randomly between the corresponding J queues", at most one per queue per time unit (p.3), independent across queues (p.5) → independent Bernoulli(a/J) arrivals at each of the 2J external queues, i.i.d. over time units; reason: the p.5 independence rules out one multinomial arrival per end
--   - reading: sup over 0 ≤ s ≤ t ≤ T → integer times s ≤ t ≤ T; reason: the process is indexed by t ∈ ℤ₊ (p.1, p.5) and (19) sums over t = 0, …, T
--   - encoding: the probability space of the queueing process → any probability space carrying i.i.d. arrival vectors with law arrivalLaw a J; reason: the event G_M depends on the arrivals only; same probability
-- source:
--   Bramson, D'Auria, Walton, Stability and Instability of the MaxWeight Policy, arXiv:1909.10825v2, display (16), p.7

import Mathlib
import Definitions.Def_MaxWeightInstab_IsGoodArrivals
import Definitions.Def_MaxWeightInstab_arrivalLaw

namespace MaxWeightInstab

/-- **Display (16)** (Bramson, D'Auria & Walton, arXiv:1909.10825v2, p.7). "It follows immediately from Lemma 1 that
`ℙ(G_M) ≥ 1 − e^{−ηT}`, for a new choice of η > 0": for the arrival process of Figure 1 (the
external arrival vectors of successive time units i.i.d. with law `arrivalLaw a J`), the event
`G_M` of (15) has probability at least `1 − e^{−ηT}` once `T ≥ C`.

**Formalization Note.** Hypotheses (4), (5) and γ with (11) are the standing assumptions of §3.1
(pp.6–7). `η` and `C` are chosen after `ε` (`G_M` uses `δ = εb`) and before `M`; `T = horizon a ν M`
(14). The arrival vector of time unit `n` is `E n` (`E 0` is not used by `G_M`). Stated for every
`ε > 0` and any probability space carrying the arrivals. -/
theorem eq_16 (J ν : ℕ) (a γ : ℝ) (h4 : rRho a ν < 1)
    (h5ν : 1 < ν ∧ ν < J)
    (h5a : (J : ℝ) / (2 * J - ν) < a ∧
      a < 1 - ((J : ℝ) + ν) * ((J : ℝ) + (ν : ℝ) ^ 2) / ((ν : ℝ) * ((J : ℝ) ^ 2 + J + (ν : ℝ) ^ 2)))
    (h11 : 1 < γ ∧ γ < a / (1 - a + a * ν / J)) :
    ∀ ε : ℝ, 0 < ε → ∃ η > 0, ∃ C : ℝ, ∀ M : ℝ, C ≤ horizon a ν M →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        [MeasureTheory.IsProbabilityMeasure P] (E : ℕ → Ω → ExtArrivals J),
        (∀ n, Measurable (E n)) → ProbabilityTheory.iIndepFun E P →
        (∀ n, P.map (E n) = (arrivalLaw a J).toMeasure) →
        1 - Real.exp (-η * horizon a ν M) ≤
          (P {ω | IsGoodArrivals a J ν γ ε M (fun n => E n ω)}).toReal := by sorry

end MaxWeightInstab
