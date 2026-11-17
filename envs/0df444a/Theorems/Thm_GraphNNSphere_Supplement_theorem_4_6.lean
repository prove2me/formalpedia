-- Prove2me | Theorems.Thm_GraphNNSphere_Supplement_theorem_4_6
-- name    : GraphNNSphere.Supplement.theorem_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:53:54.286477+00:00
-- url     : https://prove2.me/theorems/8ceb3f68-201e-4d68-a01c-5439b50b1770
-- title:
--   Theorem 4.6, p.45 — navigation by a graph built from nested subsamples
-- statement:
--   Fix $c>0$, $\beta^*(c)<\beta<1$ and $k\ge1$; let $d=\lfloor c\log n\rfloor$ and $\Delta=\lceil n^\beta\rceil$. For every sequence of probability laws $P_n=f_n\sigma_{d-1}$ with $0\le f_n\le e^{\vartheta_n}$ almost everywhere, where $\vartheta_n=o(d)$, there is a navigation graph $G$ on the data, with neighbor lists of at most $\Delta$ entries and built without using the query distribution, with the following property. For every query law $Q_n$ fixed before the data with $dQ_n/d\sigma_{d-1}\le e^{o(d)}$ almost everywhere, with probability $1-e^{-\Omega(d)}$ over the data the graph $G$ succeeds from every entry for every query outside a Borel set of $Q_n$-measure $e^{-\Omega(d)}$, within $O(1)$ moves and with evaluation cost $O(\Delta)$. In particular this holds on $\mathcal D(0,\kappa)$ for every fixed $\kappa\ge0$, whose members satisfy $f\le e^{\vartheta_d}$.
--
--   Unlike $N_\Delta$, this construction handles regions of arbitrarily low or zero density at every degree exponent strictly between $\beta^*(c)$ and $1$, provided the density is at most $e^{o(d)}$.
--
--   **Formalization Note** The graph is a measurable map from samples to neighbor lists, chosen after $P_n$ and before the query law, so it cannot depend on $Q_n$ or on the query. The density bound on $Q_n$ is written $Q_n(A)\le e^{\omega_n}\sigma_{d-1}(A)$ with $\omega_n=o(d)$.
--
--   Differences from the source:
--   - encoding: O(·), o(1), Ω(d), e^{o(d)}, "with probability 1 − o(1)", "for all sufficiently large n" → explicit constants and vanishing sequences in the quantifier order of §2.1 (fixed parameters, constants, d(·), vanishing sequences, ∀ᶠ n), probabilities as measures of explicit measurable events; reason: Lean convention, as in the published goal Theorem 3.1
--   - reading: "a navigation graph G on the data … built without using the query distribution" → a measurable map Γ_n from samples to graphs (each list of size ≤ Δ, no self-loops), which may use P_n and is chosen before Q_n; reason: the graph must be a function of the data for "with probability over the data" to be an event; the paper's construction is of this form
--   - reading: constants of e^{−Ω(d)}, O(1), O(Δ) → chosen after (c, β, k) and before ϑ, the laws and the query law; reason: §2.1: constants depend on k, c and the fixed exponents
--   - generalization: hypotheses on P_n (probability law, f_n ≤ e^{ϑ_n}) and on Q_n for every n → required only for all large n; reason: the conclusion is asymptotic; laws with the properties for every n have them eventually
--   - encoding: dQ_n/dσ_{d−1} ≤ e^{o(d)} a.e. → Q_n(A) ≤ e^{ω_n} σ_{d−1}(A) for measurable A, ω_n = o(d); reason: equivalent to the density bound
--   - encoding: O(1) moves, evaluation cost O(Δ) → moves ≤ H, evaluations ≤ CΔ; reason: explicit constants
--   - encoding: measurable / Borel query sets → MeasurableSet on the sphere (the subtype of ℝ^d with its Borel σ-algebra); reason: same sets
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), Theorem 4.6, p.45 (PDF p.47)

import Mathlib
import Definitions.Def_GraphNNSphere_IsNavGraph
import Definitions.Def_GraphNNSphere_maxDeg
import Definitions.Def_GraphNNSphere_greedyRun
import Definitions.Def_GraphNNSphere_betaStar
import Definitions.Def_GraphNNSphere_logDim
import Definitions.Def_GraphNNSphere_Supplement_sampleLaw

open MeasureTheory Filter Topology Asymptotics

namespace GraphNNSphere

namespace Supplement

/-- Theorem 4.6, navigation by a graph built from nested subsamples (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), Theorem 4.6, p.45).
Let `d = ⌊c log n⌋`, `β*(c) < β < 1`, `Δ = ⌈n^β⌉`. For every sequence of laws `P_n = f_n σ` with
`0 ≤ f_n ≤ e^{ϑ_n}` a.e., `ϑ_n = o(d)`, there is a navigation graph on the data, with lists of at most
`Δ` entries and built without the query law, such that for every query law `Q_n` fixed before the data
with `dQ_n/dσ ≤ e^{o(d)}` a.e., with probability `1 - e^{-Ω(d)}` the graph succeeds from every entry for
every query outside a Borel set of `Q_n`-measure `e^{-Ω(d)}`, within `O(1)` moves and evaluation cost
`O(Δ)`. In particular this holds on `D(0, κ)` for every fixed `κ ≥ 0`, whose members satisfy
`f ≤ e^{ϑ_d}`.

**Formalization Note** The graph is a map `Γ_n` from the sample to neighbor lists, measurable (each
graph value is attained on a measurable set of samples); it may use `P_n`, and it is chosen before
the query law, so it cannot depend on `Q_n` or on `q`. `dQ_n/dσ ≤ e^{ω_n}` is written
`Q_n(A) ≤ e^{ω_n} σ(A)` for measurable `A`. The constants come before `ϑ` and the laws. -/
theorem theorem_4_6 :
    ∀ c β : ℝ, 0 < c → betaStar c < β → β < 1 → ∀ k : ℕ, 1 ≤ k →
      ∃ c₁ c₂ H C : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ 0 < H ∧ 0 < C ∧
      ∀ ϑ : ℕ → ℝ, ϑ =o[atTop] (fun n : ℕ => (logDim c n : ℝ)) →
      ∀ f : ∀ n, Sph (logDim c n) → ℝ,
        (∀ᶠ n in atTop, IsDensity (logDim c n) (f n) ∧
          ∀ᵐ x ∂(unif (logDim c n)), f n x ≤ Real.exp (ϑ n)) →
      ∃ Γ : ∀ n, (Fin n → Sph (logDim c n)) → NavGraph n,
        (∀ n (X : Fin n → Sph (logDim c n)),
          IsNavGraph (Γ n X) ∧ maxDeg (Γ n X) ≤ ⌈(n : ℝ) ^ β⌉₊) ∧
        (∀ n (g : NavGraph n), MeasurableSet {X : Fin n → Sph (logDim c n) | Γ n X = g}) ∧
        ∀ Q : ∀ n, Measure (Sph (logDim c n)), (∀ᶠ n in atTop, IsProbabilityMeasure (Q n)) →
          (∃ ω : ℕ → ℝ, ω =o[atTop] (fun n : ℕ => (logDim c n : ℝ)) ∧
            ∀ᶠ n in atTop, ∀ A : Set (Sph (logDim c n)), MeasurableSet A →
              Q n A ≤ ENNReal.ofReal (Real.exp (ω n)) * unif (logDim c n) A) →
          ∀ᶠ n : ℕ in atTop,
            ∃ E : Set (Fin n → Sph (logDim c n)), MeasurableSet E ∧
              1 - Real.exp (-(c₁ * (logDim c n : ℝ))) ≤ (dataLawF n (logDim c n) (f n) E).toReal ∧
              ∀ X ∈ E, ∃ B : Set (Sph (logDim c n)), MeasurableSet B ∧
                (Q n B).toReal ≤ Real.exp (-(c₂ * (logDim c n : ℝ))) ∧
                ∀ q ∉ B, ∀ x₀ : Fin n, ∃ moves expansions evals : ℕ,
                  greedyRun (Γ n X) X q k x₀ = .success moves expansions evals ∧
                  (moves : ℝ) ≤ H ∧ (evals : ℝ) ≤ C * (⌈(n : ℝ) ^ β⌉₊ : ℝ) := by sorry

end Supplement

end GraphNNSphere
